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

import kotlinx.serialization.SerializationStrategy
import kotlinx.serialization.modules.EmptySerializersModule
import kotlinx.serialization.serializer
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.encoding.SmtDataEncoder
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.encoding.SmtDataSerializationMode

/** Represents a serialized member of [SmtIntermediateRepresentation] */
sealed class SmtIntermediateMember {

  class Reference(val refID: Int) : SmtIntermediateMember()

  class Value(val value: Any, val primitive: SmtPrimitive) : SmtIntermediateMember()

  class EnumValue(val value: Enum<*>) : SmtIntermediateMember()

  sealed class List(val refID: Int) : SmtIntermediateMember() {

    class ValueList(refID: Int, val primitive: SmtPrimitive, val list: MutableCollection<Any>) :
        List(refID)

    class ReferenceList(refID: Int, val list: MutableCollection<Int>) : List(refID)

    class EmptyList(refID: Int) : List(refID)
  }
}

/** Represents the serialization of [ref] */
class SmtIntermediateRepresentation(
    val ref: SmtTranslatableBase,
    val members: MutableMap<String, SmtIntermediateMember> = mutableMapOf()
)

/** Generate the intermediate representation of [ref] */
inline fun <reified T : SmtTranslatableBase> getSmtIntermediateRepresentation(
    ref: T
): List<SmtIntermediateRepresentation> {
  val serializersModule = EmptySerializersModule()
  val serializer = serializersModule.serializer<T>()
  return getSmtIntermediateRepresentation(serializer, ref)
}

/** Generate the intermediate representation of [ref] */
fun <T : SmtTranslatableBase> getSmtIntermediateRepresentation(
    serializer: SerializationStrategy<T>,
    ref: T
): List<SmtIntermediateRepresentation> {
  val result = mutableListOf<SmtIntermediateRepresentation>()
  val capturedSorts = mutableSetOf<String>()
  val encoder =
      SmtDataEncoder(
          result,
          capturedSorts,
          mutableMapOf(),
          EmptySerializersModule(),
          SmtIntermediateRepresentation(ref),
          -1,
          arrayOf(),
          null,
          SmtDataSerializationMode.DEFAULT,
          ref)
  serializer.serialize(encoder, ref)
  return result
}
