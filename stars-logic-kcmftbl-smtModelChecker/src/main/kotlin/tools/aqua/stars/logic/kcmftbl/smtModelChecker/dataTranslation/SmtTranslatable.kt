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

import kotlin.reflect.KProperty1

abstract class SmtTranslatable {

  private var smtId: Int? = null
  private var smtType: String? = null
  private val registeredMembers = mutableMapOf<String, ObjectReference>()

  companion object {

    private var nextId = 0

    fun uniqueId() = nextId++

    fun resetIds() = run { nextId = 0 }
  }

  // Can be overwritten to register Members
  open fun registerMembers() {}

  protected fun <T1 : SmtTranslatable, T2 : SmtTranslatable> T1.registerCollection(
      prop: KProperty1<T1, Collection<T2>>
  ) =
      prop.get(this).let {
        RefLst(uniqueId(), it).let { this@SmtTranslatable.registeredMembers[prop.name] = it }
      }

  protected fun <T1 : SmtTranslatable, T2 : SmtTranslatable> T1.register(prop: KProperty1<T1, T2>) =
      prop.get(this).let { Ref(it).let { registeredMembers[prop.name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerBoolean(prop: KProperty1<T1, Boolean>) =
      prop.get(this).let { Val(it).let { registeredMembers[prop.name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerNumber(prop: KProperty1<T1, Number>) =
      prop.get(this).let { Val(it).let { registeredMembers[prop.name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerString(prop: KProperty1<T1, String>) =
      prop.get(this).let { Val(it).let { registeredMembers[prop.name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerEnum(prop: KProperty1<T1, Enum<*>>) =
      prop.get(this).let { Enm(it).let { registeredMembers[prop.name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerBooleanCollection(
      prop: KProperty1<T1, Collection<Boolean>>
  ) = prop.get(this).let { Lst(uniqueId(), it).let { registeredMembers[prop.name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerNumberCollection(
      prop: KProperty1<T1, Collection<Number>>
  ) = prop.get(this).let { Lst(uniqueId(), it).let { registeredMembers[prop.name] = it } }

  protected fun <T1 : SmtTranslatable> T1.registerStringCollection(
      prop: KProperty1<T1, Collection<String>>
  ) = prop.get(this).let { Lst(uniqueId(), it).let { registeredMembers[prop.name] = it } }

  fun toObjectRepresentation(
      objectRepresentations: MutableList<ObjectRepresentation>,
      capturedTypes: MutableSet<String>
  ) {
    if (smtId != null) {
      return
    }
    smtId = uniqueId()
    this::class.simpleName!!.let {
      smtType = it
      capturedTypes.add(it)
    }
    registerMembers()
    for (entry in registeredMembers.entries) {
      when (val objectReference = entry.component2()) {
        is Ref -> {
          objectReference.ref.toObjectRepresentation(objectRepresentations, capturedTypes)
        }
        is RefLst -> {
          for (elem in objectReference.list) {
            elem.toObjectRepresentation(objectRepresentations, capturedTypes)
          }
        }
      }
    }
    objectRepresentations.add(ObjectRepresentation(this, registeredMembers))
  }
}