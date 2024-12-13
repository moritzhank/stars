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

@file:Suppress("StringLiteralDuplication", "UseDataClass")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

import tools.aqua.stars.logic.kcmftbl.smtModelChecker.SmtSolver
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.firstCharLower
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.generateEqualsITEStructure
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.toSmtLibPrimitiveFormat

/** Generate SmtLib. */
fun generateSmtLib(wrapper: SmtDataTranslationWrapper, solver: SmtSolver = SmtSolver.CVC5): String {
  val result = StringBuilder()

  // Prelude
  result.appendLine("(set-logic ALL)")
  result.appendLine()

  // Generate sort intervals
  result.appendLine("; Sort intervals")
  wrapper.capturedKClassToExternalIDInterval.forEach { (kClass, interval) ->
    // Should be in cache to this point
    val name = smtTranslationClassInfo(kClass).getTranslationName()
    result.appendLine(
        "(define-fun is_$name ((id Int)) Bool (and (>= id ${interval.first}) (<= id ${interval.second})))")
  }
  result.appendLine()

  // Generate sort members
  result.appendLine("; Sort members")
  for ((name, smtIntermediateMember) in wrapper.memberNameToSmtIntermediateMember) {
    val memberInfo = wrapper.memberNameToMemberInfo[name]!!
    when (memberInfo.memberType) {
      // Generate member definition for references
      SmtIntermediateMemberType.REFERENCE -> {
        val iteStructure =
            generateEqualsITEStructure(
                smtIntermediateMember.entries,
                "id",
                { ifEntry -> "${ifEntry.component1()}" },
                { thenEntry ->
                  "${(thenEntry.component2() as SmtIntermediateMember.Reference).refID}"
                },
                "-1")
        result.appendLine("(define-fun ${name.firstCharLower()} ((id Int)) Int $iteStructure)")
      }
      // Generate member definition for values
      SmtIntermediateMemberType.VALUE -> {
        val smtPrimitive = memberInfo.memberClass.smtPrimitive()!!
        val iteStructure =
          generateEqualsITEStructure(
            smtIntermediateMember.entries,
            "id",
            { ifPair -> "${ifPair.component1()}" },
            { thenPair ->
              (thenPair.component2() as SmtIntermediateMember.Value).value.toSmtLibPrimitiveFormat()
            }, smtPrimitive.defaultValue.toSmtLibPrimitiveFormat())
        val returnSort = smtPrimitive.smtPrimitiveSortName
        result.appendLine("(define-fun ${name.firstCharLower()} ((id Int)) $returnSort $iteStructure)")
      }
      // Generate member definition for lists
      SmtIntermediateMemberType.VALUE_LIST,
      SmtIntermediateMemberType.REFERENCE_LIST -> {
        // Generate member to list mapping
        val iteStructure =
          generateEqualsITEStructure(
            smtIntermediateMember.entries,
            "listId",
            { ifEntry -> "${ifEntry.component1()}" },
            { thenEntry ->
              "${(thenEntry.component2() as SmtIntermediateMember.List).refID}"
            },
            "-1")
        result.appendLine("(define-fun ${name.firstCharLower()} ((listId Int)) Int $iteStructure)")

        // TODO Generate *_elemInList(list, elem)
      }
      /*
        // Generate isListElement function
        val listArgumentClass = intermediate.listArgumentClass!!
        val listArgumentSort =
            listArgumentClass.smtPrimitive()?.smtPrimitiveSortName ?: listArgumentClass.simpleName
        // The outer ite structure contains ites over all possible ListRef objects. The inner ite
        // structure contains ite over all possible elements of the corresponding listRef.
        val outerITEStructure =
            generateITEStructure(
                intermediate.members,
                "x",
                { ifPair -> "list_${(ifPair.second as SmtIntermediateMember.List).refID}" },
                { thenPair ->
                  when (val member = thenPair.second as SmtIntermediateMember.List) {
                    is SmtIntermediateMember.List.ValueList -> {
                      TODO()
                    }
                    is SmtIntermediateMember.List.ReferenceList -> {
                      val refList = member.list
                      if (!refList.isEmpty()) {
                        generateITEStructure(
                            refList, "y", { ifElem -> "ind_${ifElem}" }, { _ -> "true" }, "false")
                      } else {
                        // An empty list has no elements
                        // TODO: Maybe implement possibility to omit these entries
                        "false"
                      }
                    }
                  }
                },
                "false")
        result.appendLine(
            "(define-fun ${memberName.firstCharLower()}_isListElement ((x ListRef) (y $listArgumentSort)) Bool $outerITEStructure)")
      }
    }
  }
  result.appendLine()
       */
    }
  }
  result.appendLine()

  // TODO ...

  result.appendLine("(check-sat)")
  return result.toString()
}
