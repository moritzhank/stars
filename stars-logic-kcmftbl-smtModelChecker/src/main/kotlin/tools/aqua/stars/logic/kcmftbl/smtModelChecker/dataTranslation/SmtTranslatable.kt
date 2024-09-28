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

@file:Suppress("unused")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

abstract class SmtTranslatable {

  private var smtId: Int? = null
  private val registeredMembers = mutableMapOf<String, ObjectReference>()

  companion object {

    private var nextId = 0

    fun uniqueId() = nextId++

    fun resetIds() = run { nextId = 0 }
  }

  // Can be overwritten to register Members
  open fun registerMembers() {}

  protected fun <T : SmtTranslatable> registerCollection(name: String, obj: Collection<T>) =
      obj.let { RefLst(uniqueId(), it).let { this@SmtTranslatable.registeredMembers[name] = it } }

  protected fun <T1 : SmtTranslatable, T2 : SmtTranslatable> T1.register(name: String, obj: T2) =
      obj.let { Ref(it).let { registeredMembers[name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerBoolean(name: String, obj: Boolean) =
      obj.let { Val(it).let { registeredMembers[name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerNumber(name: String, obj: Number) =
      obj.let { Val(it).let { registeredMembers[name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerString(name: String, obj: String) =
      obj.let { Val(it).let { registeredMembers[name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerEnum(name: String, obj: Enum<*>) =
      obj.let { Enm(it).let { registeredMembers[name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerBooleanCollection(
      name: String,
      obj: Collection<Boolean>
  ) = obj.let { Lst(uniqueId(), it).let { registeredMembers[name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerNumberCollection(
      name: String,
      obj: Collection<Number>
  ) = obj.let { Lst(uniqueId(), it).let { registeredMembers[name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerStringCollection(
      name: String,
      obj: Collection<String>
  ) = obj.let { Lst(uniqueId(), it).let { registeredMembers[name] = it } }

  fun toObjectRepresentation(
      objectRepresentations: MutableList<ObjectRepresentation>,
      visitedIds: Array<Boolean> = Array(nextId) { false }
  ) {
    if (smtId != null) {
      return
    }
    smtId = uniqueId()
    registerMembers()
    for (entry in registeredMembers.entries) {
      when (val objectReference = entry.component2()) {
        is Ref -> {
          objectReference.ref.toObjectRepresentation(objectRepresentations, visitedIds)
        }
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
