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
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.StructureKind
import kotlinx.serialization.descriptors.elementNames
import kotlinx.serialization.encoding.CompositeEncoder
import kotlinx.serialization.modules.SerializersModule
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.*

@OptIn(ExperimentalSerializationApi::class)
internal class SmtDataEncoder(
    result: MutableList<SmtIntermediateRepresentation>,
    capturedClasses: MutableSet<KClass<*>>,
    visitedSmtIDs: MutableMap<Int, Boolean>,
    serializersModule: SerializersModule,
    // Changing parameters:
    private val current: SmtIntermediateRepresentation?,
    private var currentMemberIndex: Int,
    private val memberNames: Array<String>,
    private var listMembers: SmtIntermediateMember.List?,
    private val serializationMode: SmtDataSerializationMode = SmtDataSerializationMode.DEFAULT,
    nextSerializable: Any? = null,
) :
    AbstractSmtDataEncoder(
        result, capturedClasses, visitedSmtIDs, serializersModule, nextSerializable) {

  private val defaultErrorMessage = {
    "An unexpected error occurred during the serialization of an object."
  }

  private fun setMember(member: SmtIntermediateMember) {
    requireNotNull(current, defaultErrorMessage)
    current.members[memberNames[currentMemberIndex++]] = member
  }

  private fun encodeSmtTranslatableBase(
      obj: SmtTranslatableBase,
      memberNames: Array<String>
  ): CompositeEncoder {
    val smtID = obj.getSmtID()
    visitedSmtIDs[smtID] = true
    val intermediateRepresentation = SmtIntermediateRepresentation(obj)
    if (serializationMode == SmtDataSerializationMode.DEFAULT) {
      // currentMemberIndex is zero for the root object
      if (currentMemberIndex >= 0) {
        setMember(SmtIntermediateMember.Reference(smtID))
      }
      result.add(intermediateRepresentation)
    } else {
      val listMembers = this.listMembers
      require(listMembers is SmtIntermediateMember.List.ReferenceList) {
        "An unexpected error occurred during the serialization of a list of non-primitive values."
      }
      listMembers.list.add(intermediateRepresentation.ref.getSmtID())
    }
    return SmtDataEncoder(
        result,
        capturedClasses,
        visitedSmtIDs,
        serializersModule,
        intermediateRepresentation,
        0,
        memberNames,
        null)
  }

  private fun encodeNextSerializableAsList(): CompositeEncoder {
    val nextSerializable = this.nextSerializable
    require(nextSerializable is List<*>) {
      "An unexpected error occurred during the serialization of a list."
    }
    val newSmtID = SmtTranslatableBase.uniqueSmtID()
    // Nested lists are not allowed up to this point (so current is not null)
    // TODO: Performance hit of about 300ms
    val typeArgument =
        current!!
            .ref
            .getSmtTranslationAnnotation()
            .getTranslatableProperties()
            .getOrNull(currentMemberIndex)
            ?.listTypeArgumentClass
    requireNotNull(typeArgument, defaultErrorMessage) // TODO: Change error message
    val primitive = typeArgument.smtPrimitive()
    val intermediateListMember =
        if (primitive != null) {
          SmtIntermediateMember.List.ValueList(newSmtID, primitive, mutableListOf())
        } else {
          SmtIntermediateMember.List.ReferenceList(newSmtID, mutableListOf())
        }
    if (serializationMode == SmtDataSerializationMode.DEFAULT) {
      setMember(intermediateListMember)
    } else {
      // This branch should not be taken, because nested lists are not allowed up to this point
      require(false, defaultErrorMessage)
      val listMembers = this.listMembers
      require(listMembers is SmtIntermediateMember.List.ReferenceList) {
        "An unexpected error occurred during the serialization of a nested list."
      }
      listMembers.list.add(intermediateListMember.refID)
    }
    return SmtDataEncoder(
        result,
        capturedClasses,
        visitedSmtIDs,
        serializersModule,
        null,
        -1,
        arrayOf(),
        intermediateListMember,
        SmtDataSerializationMode.LIST)
  }

  override fun encodeAlreadyVisitedMember(member: SmtIntermediateMember.Reference) {
    if (serializationMode == SmtDataSerializationMode.DEFAULT) {
      setMember(member)
    } else {
      val listMembers = this.listMembers
      require(listMembers is SmtIntermediateMember.List.ReferenceList) {
        "An unexpected error occurred during the serialization of a list of non-primitive values."
      }
      listMembers.list.add(member.refID)
    }
  }

  override fun encodePrimitiveValue(value: Any, primitive: SmtPrimitive?) {
    // TODO: Enums are currently encoded as ints
    if (serializationMode == SmtDataSerializationMode.DEFAULT) {
      requireNotNull(primitive) { "An unexpected non-primitive value has occurred." }
      setMember(SmtIntermediateMember.Value(value, primitive))
    } else {
      val listMembers = this.listMembers
      require(listMembers is SmtIntermediateMember.List.ValueList) {
        "An unexpected error occurred during the serialization of a list of primitive values."
      }
      require(value.smtPrimitive() == listMembers.primitive) {
        "An unexpected primitive type was encountered when serialising a list of primitive values."
      }
      listMembers.list.add(value)
    }
  }

  override fun beginStructure(descriptor: SerialDescriptor): CompositeEncoder {
    val nextSerializable = this.nextSerializable
    requireNotNull(nextSerializable, defaultErrorMessage)
    // Encode list
    if (descriptor.kind == StructureKind.LIST) {
      return encodeNextSerializableAsList()
    }
    // Throw error when encoding elements other than lists and classes
    val kind = descriptor.kind
    require(kind == StructureKind.CLASS, defaultErrorMessage)
    // Encode class
    require(nextSerializable is SmtTranslatableBase, defaultErrorMessage)
    capturedClasses.add(nextSerializable::class)
    return encodeSmtTranslatableBase(
        nextSerializable, descriptor.elementNames.toList().toTypedArray())
  }
}
