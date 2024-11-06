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
import kotlinx.serialization.descriptors.PolymorphicKind
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.StructureKind
import kotlinx.serialization.descriptors.elementNames
import kotlinx.serialization.encoding.CompositeEncoder
import kotlinx.serialization.modules.SerializersModule
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.*

@OptIn(ExperimentalSerializationApi::class)
internal class SmtDataEncoder(
    result: MutableList<SmtIntermediateRepresentation>,
    capturedSorts: MutableSet<String>,
    visitedSmtIDs: MutableMap<Int, Boolean>,
    serializersModule: SerializersModule,
    // Changing parameters
    private val current: SmtIntermediateRepresentation?,
    private var currentMemberIndex: Int,
    private val memberNames: Array<String>,
    private var listMembers: SmtIntermediateMember.List?,
    private val serializationMode: SmtDataSerializationMode = SmtDataSerializationMode.DEFAULT,
    nextSerializable: Any? = null,
) :
    AbstractSmtDataEncoder(
        result, capturedSorts, visitedSmtIDs, serializersModule, nextSerializable) {

  private fun setMember(member: SmtIntermediateMember) {
    requireNotNull(current) {
      "An unexpected error occurred during the serialization of an object."
    }
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
        capturedSorts,
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
    val intermediateListMember =
        if (nextSerializable.size == 0) {
          SmtIntermediateMember.List.EmptyList(newSmtID)
        } else {
          val primitiveOfFirstElement = nextSerializable.first()!!.smtPrimitive()
          if (primitiveOfFirstElement != null) {
            SmtIntermediateMember.List.ValueList(newSmtID, primitiveOfFirstElement, mutableListOf())
          } else {
            SmtIntermediateMember.List.ReferenceList(newSmtID, mutableListOf())
          }
        }
    if (serializationMode == SmtDataSerializationMode.DEFAULT) {
      setMember(intermediateListMember)
    } else {
      val listMembers = this.listMembers
      require(listMembers is SmtIntermediateMember.List.ReferenceList) {
        "An unexpected error occurred during the serialization of a nested list."
      }
      listMembers.list.add(intermediateListMember.refID)
    }
    return SmtDataEncoder(
        result,
        capturedSorts,
        visitedSmtIDs,
        serializersModule,
        null,
        -1,
        arrayOf(),
        intermediateListMember,
        SmtDataSerializationMode.LIST)
  }

  private fun getCurrentMemberNameFullQualified(): String {
    requireNotNull(current) { "Could not access members." }
    val memberName = memberNames.getOrNull(currentMemberIndex) ?: "<unknown_member>"
    val className = current.ref::class.simpleName ?: "<unknown_class>"
    return "$className.$memberName"
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
    // TODO: What about enums? They are currently encoded as ints.
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
    requireNotNull(nextSerializable) {
      "An unexpected error occurred during the serialization of an object."
    }
    // Encode list
    if (descriptor.kind == StructureKind.LIST) {
      return encodeNextSerializableAsList()
    }
    // Throw error when encoding maps or singletons
    val kind = descriptor.kind
    require(kind == StructureKind.CLASS || kind == PolymorphicKind.SEALED) {
      "Maps or singletons can not be translated. You can solve this by annotating \"${getCurrentMemberNameFullQualified()}\" with @Transient."
    }
    // Encode class
    require(nextSerializable is SmtTranslatableBase) {
      val memberName = "${descriptor.serialName}.${descriptor.getElementName(currentMemberIndex)}"
      val className = nextSerializable::class.simpleName ?: "<unknown_class>"
      "The class \"$className\" (Accessed via member \"$memberName\") has to inherit from SmtTranslatableBase in order to be serialized."
    }
    return encodeSmtTranslatableBase(
        nextSerializable, descriptor.elementNames.toList().toTypedArray())
  }
}
