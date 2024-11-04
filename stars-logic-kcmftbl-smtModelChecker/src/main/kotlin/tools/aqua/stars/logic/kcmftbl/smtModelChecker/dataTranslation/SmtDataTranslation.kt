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

import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.SerializationStrategy
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.AbstractEncoder
import kotlinx.serialization.encoding.CompositeEncoder
import kotlinx.serialization.modules.EmptySerializersModule
import kotlinx.serialization.modules.SerializersModule
import kotlinx.serialization.serializer

// Test
inline fun <reified T : Any> test(ref: T) {
  val serializersModule = EmptySerializersModule()
  val serializer = serializersModule.serializer<T>()
  test(serializer, ref)
}

fun <T : Any> test(serializer: SerializationStrategy<T>, ref: T) {
  val idRegistry = IDRegistry()
  val result = mutableListOf<SmtIntermediateRepresentation>()
  val encoder = SmtDataEncoder(
      result,
      mutableSetOf(),
      idRegistry,
      SmtIntermediateRepresentation.Reference(idRegistry.get(ref))
  )
  serializer.serialize(encoder, ref)
}

@OptIn(ExperimentalSerializationApi::class)
internal class SmtDataEncoder(
    private val result: MutableList<SmtIntermediateRepresentation>,
    private val capturedSorts: MutableSet<String>,
    private val idRegistry: IDRegistry,
    private val current: SmtIntermediateRepresentation,
    override val serializersModule: SerializersModule = EmptySerializersModule()
) : AbstractEncoder() {

  //Check if element should be encoded
  override fun <T> encodeSerializableElement(
    descriptor: SerialDescriptor,
    index: Int,
    serializer: SerializationStrategy<T>,
    value: T
  ) {
    require(value is Any)
    if (!idRegistry.hasID(value)) {
      encodeSerializableValue(serializer, value)
    }
  }

  //Check if (nullable) element should be encoded
  override fun <T : Any> encodeNullableSerializableElement(
    descriptor: SerialDescriptor,
    index: Int,
    serializer: SerializationStrategy<T>,
    value: T?
  ) {
    if (value != null && !idRegistry.hasID(value)) {
      encodeSerializableValue(serializer, value)
    }
  }

  override fun encodeValue(value: Any) {
    // distinguish between modes and primitive value
    println("--encodeValue($value)")
  }

  override fun beginStructure(descriptor: SerialDescriptor): CompositeEncoder {
    println("beginStructure(${descriptor.serialName})")
    return this
  }

  override fun endStructure(descriptor: SerialDescriptor) {
    println("endStructure(${descriptor.serialName})")
  }
}
