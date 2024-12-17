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

import kotlin.reflect.KClass

/** Groups IDs of [SmtIntermediateRepresentation] by type/sort. */
class SmtDataTranslationWrapper(intermediateRepresentation: List<SmtIntermediateRepresentation>) {

  /** Maps member names to the associated [SmtIntermediateMember]s with SMT-IDs of the parent. */
  val memberNameToSmtIntermediateMember =
      mutableMapOf<String, MutableMap<Int, SmtIntermediateMember>>()
  /** Maps captured classes to their interval of external IDs. */
  val capturedKClassToExternalIDInterval = mutableMapOf<KClass<*>, Pair<Int, Int>>()
  /** Maps SMT-IDs to their external IDs. */
  val smtIDToExternalID = mutableMapOf<Int, Int>()
  /** Contains [MemberInfo] for each member name. */
  val memberNameToMemberInfo = mutableMapOf<String, MemberInfo>()
  /** Contains all present lists. */
  val presentListMemberNames = mutableSetOf<String>()

  init {
    val capturedLists = mutableListOf<SmtIntermediateMember.List>()
    // Calculate memberNamesToIndividuals & memberNameToMemberInfo
    // presentLists is also calculated here
    intermediateRepresentation.forEach { intermediate ->
      val parentClassInfo = smtTranslationClassInfo(intermediate.ref::class)
      val parentSmtID = intermediate.ref.getSmtID()
      parentClassInfo.getTranslatableProperties().forEach { property ->
        val propertySmtName = "${parentClassInfo.getTranslationName()}_${property.name}"
        val intermediateMember = intermediate.members.getValue(property.name)
        memberNameToSmtIntermediateMember
            .computeIfAbsent(propertySmtName) {
              // Compute memberNameToMemberInfo once for a member
              memberNameToMemberInfo[propertySmtName] =
                  MemberInfo(
                      intermediateMember.type(), property.clazz, property.listTypeArgumentClass)
              mutableMapOf()
            }[parentSmtID] = intermediateMember
        if (intermediateMember is SmtIntermediateMember.List) {
          presentListMemberNames.add(propertySmtName)
          capturedLists.add(intermediateMember)
        }
      }
    }
    // Calculate number of occurrences of all classes
    val capturedKClassesToOccurrence = mutableMapOf<KClass<*>, Int>()
    intermediateRepresentation.forEach { intermediate ->
      val kClass = intermediate.ref::class
      capturedKClassesToOccurrence[kClass] = capturedKClassesToOccurrence.getOrPut(kClass) { 0 } + 1
    }
    capturedKClassesToOccurrence[List::class] = capturedLists.size
    // Calculate capturedKClassToExternalIDInterval
    var newExternalId = 0
    capturedKClassesToOccurrence.forEach { (kClass, occurrence) ->
      val interval = Pair(newExternalId, newExternalId + occurrence - 1)
      capturedKClassToExternalIDInterval[kClass] = interval
      newExternalId += occurrence
    }
    // Calculate external IDs for each intermediate representation
    intermediateRepresentation.forEach { intermediate ->
      val kClass = intermediate.ref::class
      val offsetID = capturedKClassesToOccurrence[kClass]!! - 1
      capturedKClassesToOccurrence[kClass] = offsetID
      val externalID = capturedKClassToExternalIDInterval[kClass]!!.first + offsetID
      smtIDToExternalID[intermediate.ref.getSmtID()] = externalID
    }
    // Calculate external IDs for each list
    capturedLists.forEach { list ->
      val offsetID = capturedKClassesToOccurrence[List::class]!! - 1
      capturedKClassesToOccurrence[List::class] = offsetID
      val externalID = capturedKClassToExternalIDInterval[List::class]!!.first + offsetID
      smtIDToExternalID[list.refID] = externalID
    }
  }

  /** Captures (for the translation) essential information about a member. */
  @Suppress("UseDataClass")
  class MemberInfo(
      /** Type of the member (see [SmtIntermediateMemberType]). */
      val memberType: SmtIntermediateMemberType,
      /** Class of the represented member. */
      val memberClass: Class<*>,
      /** Class of the generic argument (if existing) of the represented member. */
      val listArgumentClass: Class<*>?,
  )
}
