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

@file:Suppress(
    "unused",
    "OutdatedDocumentation",
    "UndocumentedPublicClass",
    "UndocumentedPublicFunction",
    "UndocumentedPublicProperty",
    "UseDataClass")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

import kotlin.reflect.KClass
import kotlinx.serialization.SerializationStrategy
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.serializer
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.encoding.SmtDataEncoder
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.encoding.SmtDataSerializationMode

/** Represents the serialization of [ref]. */
class SmtIntermediateRepresentation(
    val ref: SmtTranslatableBase,
    val members: MutableMap<String, SmtIntermediateMember> = mutableMapOf()
)

/** Represents a serialized member of [SmtIntermediateRepresentation]. */
sealed class SmtIntermediateMember {

  class Reference(val refID: Int) : SmtIntermediateMember()

  class Value(val value: Any, val primitive: SmtPrimitive) : SmtIntermediateMember()

  sealed class List(val refID: Int) : SmtIntermediateMember() {

    class ValueList(refID: Int, val primitive: SmtPrimitive, val list: MutableCollection<Any>) :
        List(refID)

    class ReferenceList(refID: Int, val list: MutableCollection<Int>) : List(refID)
  }

  fun type(): SmtIntermediateMemberType =
      when (this) {
        is Reference -> SmtIntermediateMemberType.REFERENCE
        is Value -> SmtIntermediateMemberType.VALUE
        is List.ValueList -> SmtIntermediateMemberType.VALUE_LIST
        is List.ReferenceList -> SmtIntermediateMemberType.REFERENCE_LIST
      }
}

/**
 * Enum to streamline the handling of [SmtIntermediateMember] in the following translation process.
 */
enum class SmtIntermediateMemberType {

  REFERENCE,
  VALUE,
  VALUE_LIST,
  REFERENCE_LIST
}

/**
 * Generate the intermediate representation of [ref].
 *
 * @param capturedClasses All classes found will be added to this set
 * @param capturedLists All lists found will be added to this list
 */
inline fun <reified T : SmtTranslatableBase> getSmtIntermediateRepresentation(
    serializersModule: SerializersModule,
    ref: T,
    capturedClasses: MutableSet<KClass<*>>,
    capturedLists: MutableList<SmtIntermediateMember.List>
): List<SmtIntermediateRepresentation> {
  val serializer = serializersModule.serializer<T>()
  return getSmtIntermediateRepresentation(
      serializer, serializersModule, ref, capturedClasses, capturedLists)
}

/**
 * Generate the intermediate representation of [ref].
 *
 * @param capturedClasses All classes found will be added to this set
 * @param capturedLists All lists found will be added to this list
 */
fun <T : SmtTranslatableBase> getSmtIntermediateRepresentation(
    serializer: SerializationStrategy<T>,
    serializersModule: SerializersModule,
    ref: T,
    capturedClasses: MutableSet<KClass<*>>,
    capturedLists: MutableList<SmtIntermediateMember.List>
): List<SmtIntermediateRepresentation> {
  val result = mutableListOf<SmtIntermediateRepresentation>()
  val encoder =
      SmtDataEncoder(
          result,
          capturedClasses,
          capturedLists,
          mutableMapOf(),
          serializersModule,
          SmtIntermediateRepresentation(ref),
          -1,
          arrayOf(),
          null,
          SmtDataSerializationMode.DEFAULT,
          ref)
  serializer.serialize(encoder, ref)
  return result
}
