/*
 * Copyright 2024 The STARS Project Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

@file:Suppress("UNCHECKED_CAST")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

import java.lang.IllegalArgumentException
import kotlin.collections.Collection
import kotlin.reflect.KClass
import kotlin.reflect.KProperty1
import kotlin.reflect.KVisibility
import kotlin.reflect.full.hasAnnotation
import kotlin.reflect.full.isSubtypeOf
import kotlin.reflect.typeOf

interface ObjectReference

class Ref(val id: Int) : ObjectReference

class Val(val value: Any) : ObjectReference

class Col(val id: Int, val list: Collection<*>) : ObjectReference

class ObjectRepresentation(val id: Int, val ref: Any, val member: Map<String, ObjectReference>)

class ObjectRepresentationGenerator(val obj: Any) {

  // Every object gets assigned a unique id, that is equivalent to its position in resulting array
  private var nextId = 1
  // Cannot use Maps (HashMaps) because the hashCode() function leads to infinite recursion in
  // certain cases
  private val objectToId = mutableListOf<Pair<Any, Int>>()

  private val result = mutableListOf<ObjectRepresentation>()
  private val queue = mutableListOf(obj)

  private fun queueIfUnregistered(obj: Any, current: Any) {
    println(obj)
    if (obj === current || queue.any { it === obj } || result.any { it.ref === obj }) {
      return
    }
    queue.add(obj)
  }

  private fun <T> Collection<Pair<Any, T>>.getEntry(obj: Any): T? {
    this.forEach {
      if (it.first === obj) {
        return it.second
      }
    }
    return null
  }

  private fun getId(obj: Any): Int {
    val id = objectToId.getEntry(obj)
    if (id != null) {
      return id
    }
    return nextId++.apply { objectToId.add(Pair(obj, this)) }
  }

  init {
    while (queue.isNotEmpty()) {
      val current = queue.removeFirst()
      val members =
          current::class.members.filterIsInstance<KProperty1<*, *>>().filter {
            it.visibility == KVisibility.PUBLIC
          }
      val members_or = mutableMapOf<String, ObjectReference>()
      for (member in members) {
        if (member.hasAnnotation<SmtIgnore>()) {
          continue
        }
        val isTranslatable =
            (member.returnType.classifier as KClass<*>).hasAnnotation<SmtTranslatable>()
        val instanceOfMember: Any = (member as KProperty1<Any, *>).get(current) ?: continue
        // Member is not marked as translatable
        if (!isTranslatable) {
          // Member is primitive
          if (member.returnType == typeOf<String>() ||
              member.returnType.isSubtypeOf(typeOf<Number>()) ||
              member.returnType == typeOf<Boolean>()) {
            members_or[member.name] = Val(instanceOfMember)
            // Member is collection
          } else if (member.returnType.isSubtypeOf(typeOf<Collection<*>>())) {
            val id = getId(instanceOfMember)
            members_or[member.name] = Col(id, instanceOfMember as Collection<*>)
            for (elem in instanceOfMember) {
              if (elem == null) {
                continue
              }
              queueIfUnregistered(elem, current)
            }
            // Member is other reference not marked with translatable
          } else {
            throw IllegalArgumentException(
                "${member.returnType} is not supported for object representation. You can use @SmtIgnore to prevent this exception.")
          }
          continue
        }
        // Member is translatable reference
        val id = getId(instanceOfMember)
        members_or[member.name] = Ref(id)
        queueIfUnregistered(instanceOfMember, current)
      }
      val current_or = ObjectRepresentation(getId(current), current, members_or)
      result.add(current_or)
    }
  }

  fun getResult() = result.sortedBy { it.id }.toTypedArray()
}
