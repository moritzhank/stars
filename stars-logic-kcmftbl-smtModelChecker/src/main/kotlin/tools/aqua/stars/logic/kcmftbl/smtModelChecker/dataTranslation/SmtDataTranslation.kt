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
      // TODO
      else -> {}
    }
  }
  result.appendLine()

  // TODO ...

  result.appendLine("(check-sat)")
  return result.toString()
}
