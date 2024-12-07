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

import kotlin.reflect.KClass
import kotlinx.serialization.*
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.StructureKind
import kotlinx.serialization.descriptors.elementNames
import kotlinx.serialization.encoding.AbstractEncoder
import kotlinx.serialization.modules.SerializersModule
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.*

/** Abstracts the verification and handling of the next serializable value ([nextSerializable]) */
@ExperimentalSerializationApi
internal abstract class AbstractSmtDataEncoder(
    protected val result: MutableList<SmtIntermediateRepresentation>,
    protected val capturedClasses: MutableSet<KClass<*>>,
    protected val capturedLists: MutableList<SmtIntermediateMember.List>,
    protected val visitedSmtIDs: MutableMap<Int, Boolean>,
    override val serializersModule: SerializersModule,
    protected var nextSerializable: Any? = null
) : AbstractEncoder() {

  /** This function is called for each member encountered that has already been serialized */
  abstract fun encodeAlreadyVisitedMember(member: SmtIntermediateMember.Reference)

  abstract fun encodePrimitiveValue(value: Any, primitive: SmtPrimitive?)

  private fun requireSameRegisteredElements(
      descriptor: SerialDescriptor,
      smtAnnotation: SmtTranslationAnnotation,
      lazyMessage: (List<String>, List<String>) -> Any
  ) {
    val descriptorElementNames = descriptor.elementNames.toList()
    val annotationElementNames =
        smtAnnotation.getTranslatableProperties().fold(mutableListOf<String>()) { list, elem ->
          list.apply { add(elem.name) }
        } as List<String>
    require(descriptorElementNames == annotationElementNames) {
      lazyMessage(annotationElementNames, descriptorElementNames)
    }
  }

  /** Verifies all requirements for serialized elements and handles already visited elements */
  final override fun <T> encodeSerializableElement(
      descriptor: SerialDescriptor,
      index: Int,
      serializer: SerializationStrategy<T>,
      value: T
  ) {
    nextSerializable = null
    requireNotNull(value) {
      "The current serialized value should not be null. This is probably a bug in kotlinx.serialization."
    }
    val elemDescriptor = descriptor.getElementDescriptor(index)
    if (elemDescriptor.kind == StructureKind.CLASS) {
      require(value is SmtTranslatableBase) {
        val className = value::class.simpleName ?: "<unknown_class>"
        val memberName = "${descriptor.serialName}.${descriptor.getElementName(index)}"
        "The class \"$className\" (Accessed via \"$memberName\") has to inherit from SmtTranslatableBase in order to be serialized."
      }
      // TODO: This is not verified for root object
      // TODO: Performance hit of about 250ms
      requireSameRegisteredElements(elemDescriptor, value.getSmtTranslationAnnotation()) { l1, l2 ->
        val className = value::class.simpleName ?: "<unknown_class>"
        val memberName = "${descriptor.serialName}.${descriptor.getElementName(index)}"
        "The list of expected members does not match the serialised members for \"$className\" (Accessed via \"$memberName\"). Expected: $l1. Found: $l2. This may be due to incorrect configuration of a custom serializer or missing @Transient annotations."
      }
      val smtID = value.getSmtID()
      if (visitedSmtIDs[smtID] == true) {
        encodeAlreadyVisitedMember(SmtIntermediateMember.Reference(smtID))
        return
      }
      require(elemDescriptor.kind != StructureKind.LIST) {
        val memberName = "${descriptor.serialName}.${descriptor.getElementName(index)}"
        "Generic (except lists), anonymous and polymorphic classes can not be translated. You can solve this by annotating \"$memberName}\" with @Transient."
      }
    }
    nextSerializable = value
    super.encodeSerializableElement(descriptor, index, serializer, value)
  }

  final override fun <T : Any> encodeNullableSerializableElement(
      descriptor: SerialDescriptor,
      index: Int,
      serializer: SerializationStrategy<T>,
      value: T?
  ) {
    TODO()
  }

  final override fun encodeValue(value: Any) {
    nextSerializable = null
    encodePrimitiveValue(value, value.smtPrimitive())
  }
}
