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
  private var registeredMembers = mutableMapOf<String, ObjectReference>()

  companion object {

    private var nextId = 0

    fun uniqueId() = nextId++

    fun resetIds() = run { nextId = 0 }
  }

  // Can be overwritten to register Members
  open fun registerMembers() {}

  fun getSmtId(): Int? = smtId

  fun getSmtType(): String? = smtType

  /** Using this function may cause undesirable behavior! */
  protected fun registerMember(name: String, objRef: ObjectReference) {
    registeredMembers[name] = objRef
  }

  protected inline fun <T1 : SmtTranslatable, reified T2 : SmtTranslatable> T1.registerCollection(
      prop: KProperty1<T1, Collection<T2>>
  ) {
    val t2KClass = T2::class
    require(t2KClass.isData) {
      "${t2KClass.simpleName} has to be a data class. Only collections of data classes can be registered."
    }
    prop.get(this).let {
      RefLst(uniqueId(), t2KClass.simpleName!!, it).let {
        this@SmtTranslatable.registerMember(prop.name, it)
      }
    }
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
  ) =
      prop.get(this).let {
        Lst(uniqueId(), PrimitiveSmtSort.BOOL, it).let { registeredMembers[prop.name] = it }
      }

  protected fun <T1 : SmtTranslatable> T1.registerIntCollection(
      prop: KProperty1<T1, Collection<Int>>
  ) =
      prop.get(this).let {
        Lst(uniqueId(), PrimitiveSmtSort.INT, it).let { registeredMembers[prop.name] = it }
      }

  protected fun <T1 : SmtTranslatable> T1.registerDoubleCollection(
      prop: KProperty1<T1, Collection<Double>>
  ) =
      prop.get(this).let {
        Lst(uniqueId(), PrimitiveSmtSort.REAL, it).let { registeredMembers[prop.name] = it }
      }

  protected fun <T1 : SmtTranslatable> T1.registerStringCollection(
      prop: KProperty1<T1, Collection<String>>
  ) =
      prop.get(this).let {
        Lst(uniqueId(), PrimitiveSmtSort.STRING, it).let { registeredMembers[prop.name] = it }
      }

  fun toObjectRepresentation(
      objectRepresentations: MutableList<ObjectRepresentation>,
      capturedTypes: MutableSet<String>,
      capturedTypesToMembers: MutableMap<String, MutableMap<String, ObjectReference>>
  ) {
    if (smtId != null) {
      return
    }
    smtId = uniqueId()
    registerMembers()
    this::class.simpleName!!.let {
      smtType = it
      if (capturedTypes.add(it)) {
        capturedTypesToMembers[it] = registeredMembers
      }
    }
    for (entry in registeredMembers.entries) {
      when (val objectReference = entry.component2()) {
        is Ref -> {
          objectReference.ref.toObjectRepresentation(
              objectRepresentations, capturedTypes, capturedTypesToMembers)
        }
        is RefLst -> {
          for (elem in objectReference.list) {
            elem.toObjectRepresentation(
                objectRepresentations, capturedTypes, capturedTypesToMembers)
          }
        }
      }
    }
    objectRepresentations.add(ObjectRepresentation(this, registeredMembers))
  }
}
