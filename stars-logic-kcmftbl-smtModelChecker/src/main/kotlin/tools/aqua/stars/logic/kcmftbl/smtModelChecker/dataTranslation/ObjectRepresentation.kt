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

import kotlin.reflect.*
import kotlin.reflect.full.createType
import kotlin.reflect.full.hasAnnotation
import kotlin.reflect.full.isSubtypeOf

interface ObjectReference

class Ref(val id: Int) : ObjectReference

class Val(val value: Any) : ObjectReference

class Lst(val id: Int, val list: Collection<*>) : ObjectReference

class Enm(val value: Any) : ObjectReference

class Nll() : ObjectReference

class ObjectRepresentation(val id: Int, val ref: Any, val member: Map<String, ObjectReference>)

class ObjectRepresentationGenerator(obj: SmtTranslatable) {

  private val result = mutableListOf<ObjectRepresentation>()
  private val queue = mutableListOf(obj)
  private val markedIds = mutableListOf(obj.smt_tid)
  private val memberCache = mutableMapOf<KClass<*>, List<KProperty1<*, *>>>()

  private fun queueIfUnmarked(obj: SmtTranslatable) {
    if (!markedIds.contains(obj.smt_tid)) {
      queue.add(obj)
      markedIds.add(obj.smt_tid)
    }
  }

  private fun KType.isPrimitive(): Boolean {
    return this == typeOf<String>() ||
        this.isSubtypeOf(typeOf<Number>()) ||
        this == typeOf<Boolean>()
  }

  private fun getMembers(cls: KClass<*>): List<KProperty1<*, *>> =
      memberCache[cls]
          ?: cls.members
              .filterIsInstance<KProperty1<*, *>>()
              .filter { it.visibility == KVisibility.PUBLIC && !it.hasAnnotation<SmtIgnore>() }
              .also { memberCache[cls] = it }

  init {
    while (queue.isNotEmpty()) {
      val current = queue.removeFirst()
      val members = getMembers(current::class)
      val memberObjectReferences = mutableMapOf<String, ObjectReference>()
      for (member in members) {
        val instanceOfMember: Any? = (member as KProperty1<Any, *>).get(current)
        // Member is null
        if (instanceOfMember == null) {
          memberObjectReferences[member.name] = Nll()
          continue
        }
        // Member is not translatable
        val isTranslatable =
          member.returnType.isSubtypeOf(typeOf<SmtTranslatable>()) ||
                  member.returnType.isSubtypeOf(typeOf<SmtTranslatable?>())
        if (!isTranslatable) {
          // Member is enum
          if (member.returnType.isSubtypeOf(typeOf<Enum<*>>())) {
            memberObjectReferences[member.name] = Enm(instanceOfMember)
            // Member is primitive
          } else if (member.returnType.isPrimitive()) {
            memberObjectReferences[member.name] = Val(instanceOfMember)
            // Member is List
          } else if (member.returnType.isSubtypeOf(typeOf<Collection<*>>())) {
            // Continue for empty list
            val firstElem: Any = (instanceOfMember as Collection<*>).firstOrNull() ?: continue
            // Check if generic type of list is primitive
            val genericType = firstElem::class.createType()
            if (!genericType.isPrimitive()) {
              // Check if generic type of list is translatable
              if (genericType.isSubtypeOf(typeOf<SmtTranslatable>())) {
                for (listElem in instanceOfMember) {
                  queueIfUnmarked(listElem as SmtTranslatable)
                }
              } else {
                throw IllegalArgumentException(
                    "$genericType as generic type is not supported for object representation. You can use @SmtIgnore to prevent this exception.")
              }
            }
            memberObjectReferences[member.name] = Lst(SmtTranslatable.uniqueId(), instanceOfMember)
          } else {
            throw IllegalArgumentException(
                "${member.returnType} is not supported for object representation. You can use @SmtIgnore to prevent this exception.")
          }
          continue
        }
        // Member is translatable reference
        memberObjectReferences[member.name] = Ref((instanceOfMember as SmtTranslatable).smt_tid)
        queueIfUnmarked(instanceOfMember)
      }
      val current_or =
          ObjectRepresentation((current as SmtTranslatable).smt_tid, current, memberObjectReferences)
      result.add(current_or)
    }
  }

  fun getResult() = result.sortedBy { it.id }.toTypedArray()
}
