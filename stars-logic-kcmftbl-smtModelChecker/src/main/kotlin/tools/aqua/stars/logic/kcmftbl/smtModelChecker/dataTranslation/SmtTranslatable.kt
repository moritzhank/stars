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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

import kotlin.reflect.KProperty1

abstract class SmtTranslatable {

  val smtId: Int = uniqueId()
  private val registeredMembers = mutableMapOf<String, ObjectReference>()

  companion object {
    private var nextId = 0

    fun uniqueId() = nextId++
  }

  // Can be overwritten to register Members
  open fun registerMembers() {}

    /*
  protected fun register(prop: KProperty1<SmtTranslatable, Boolean>) =
      Val(prop.get(this)).let { registeredMembers[prop.name] = it }
     */

  protected fun register(name: String, prop: Boolean) =
      Val(prop).let { registeredMembers[name] = it }

  protected fun register(name: String, prop: Number) =
      Val(prop).let { registeredMembers[name] = it }

  protected fun register(name: String, prop: String) =
      Val(prop).let { registeredMembers[name] = it }

  protected fun register(name: String, prop: SmtTranslatable) =
      Ref(prop.smtId, prop).let { registeredMembers[name] = it }

  protected fun register(name: String, prop: Collection<SmtTranslatable>) =
      RefLst(uniqueId(), prop).let { registeredMembers[name] = it }

  protected fun registerBooleanCollection(name: String, prop: Collection<Boolean>) =
      Lst(uniqueId(), prop).let { registeredMembers[name] = it }

  protected fun registerNumberCollection(name: String, prop: Collection<Number>) =
      Lst(uniqueId(), prop).let { registeredMembers[name] = it }

  protected fun registerStringCollection(name: String, prop: Collection<String>) =
      Lst(uniqueId(), prop).let { registeredMembers[name] = it }

  fun toObjectRepresentation(
      objectRepresentations: MutableList<ObjectRepresentation>,
      visitedIds: MutableList<Int> = mutableListOf()
  ) {
      if (visitedIds.contains(smtId)) {
          return
      } else {
          registerMembers()
          visitedIds.add(smtId)
      }
      for (entry in registeredMembers.entries) {
          val objectReference = entry.component2()
          when(objectReference) {
              is Ref -> { objectReference.ref.toObjectRepresentation(objectRepresentations, visitedIds) }
              is RefLst -> {
                  for (elem in objectReference.list) {
                      elem.toObjectRepresentation(objectRepresentations, visitedIds)
                  }
              }
          }
      }
      objectRepresentations.add(ObjectRepresentation(this, registeredMembers))
  }
}
