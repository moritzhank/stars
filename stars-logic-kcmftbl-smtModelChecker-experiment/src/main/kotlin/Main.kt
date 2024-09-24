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

import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.SmtTranslatable
import kotlin.reflect.KProperty1
import kotlin.reflect.KVisibility
import kotlin.reflect.full.hasAnnotation
import kotlin.reflect.full.isSubtypeOf
import kotlin.reflect.typeOf

fun main() {
  val x = ExperimentLoader.loadTestSegment()
  val y = listOfTranslatableObjects(x)
  println(y.size)
}

fun listOfTranslatableObjects(root: Any): List<Any> {
  val result = mutableListOf<Any>()
  val inspectNext = mutableListOf(root)
  while (inspectNext.isNotEmpty()) {
    val current: Any = inspectNext.removeFirst()
    val members = current::class.members.filterIsInstance<KProperty1<*, *>>().filter { it.visibility == KVisibility.PUBLIC && !it.isFinal }
    // iterate over all members of current
    for (member in members) {
      val instOfMember: Any = (member as KProperty1<Any, *>).get(current)!!
      if (!member.hasAnnotation<SmtTranslatable>()) {
        val type = member.returnType
        // member is primitive
        if (type == typeOf<String>() || type.isSubtypeOf(typeOf<Number>())) {
          continue
        }
        // collections
        // todo
        result.add(instOfMember)
        continue
      }
      if(instOfMember === current || result.containsInst(instOfMember) || inspectNext.containsInst(instOfMember)) {
        continue
      }
      inspectNext.add(instOfMember)
    }
    result.add(current)
  }
  return result
}

private fun <T> Collection<T>.containsInst(other: T): Boolean {
  this.forEach {
    if(it === other) {
      return true
    }
  }
  return false
}