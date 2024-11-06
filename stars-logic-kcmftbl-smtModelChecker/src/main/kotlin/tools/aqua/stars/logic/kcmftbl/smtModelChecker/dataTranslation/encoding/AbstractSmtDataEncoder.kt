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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.encoding

import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.SerializationStrategy
import kotlinx.serialization.encoding.AbstractEncoder
import kotlinx.serialization.modules.SerializersModule
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.*

/** Abstracts the handling of the next serializable value (Management of [nextSerializable]) */
@ExperimentalSerializationApi
internal abstract class AbstractSmtDataEncoder(
    protected val result: MutableList<SmtIntermediateRepresentation>,
    protected val capturedSorts: MutableSet<String>,
    protected val visitedSmtIDs: MutableMap<Int, Boolean>,
    override val serializersModule: SerializersModule,
    protected var nextSerializable: Any? = null
) : AbstractEncoder() {

  /** This function is called for each member encountered that has already been serialized */
  abstract fun encodeAlreadyVisitedMember(member: SmtIntermediateMember.Reference)

  abstract fun encodePrimitiveValue(value: Any, primitive: SmtPrimitive?)

  final override fun <T> encodeSerializableValue(serializer: SerializationStrategy<T>, value: T) {
    nextSerializable = null
    if (value is SmtTranslatableBase) {
      val smtID = value.getSmtID()
      if (visitedSmtIDs[smtID] == true) {
        encodeAlreadyVisitedMember(SmtIntermediateMember.Reference(smtID))
        return
      }
    }
    nextSerializable = value
    super.encodeSerializableValue(serializer, value)
  }

  final override fun encodeValue(value: Any) {
    nextSerializable = null
    encodePrimitiveValue(value, value.smtPrimitive())
  }
}
