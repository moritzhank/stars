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

import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.ObjectReference
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.ObjectRepresentation
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.generateSmtLib
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.runSmtSolver

fun main() {
  val result = mutableListOf<ObjectRepresentation>()
  val resultCapturedTypes = mutableSetOf<String>()
  val resultCapturedTypesToMembers = mutableMapOf<String, MutableMap<String, ObjectReference>>()
  ExperimentLoader.loadTestSegment()
      .toObjectRepresentation(result, resultCapturedTypes, resultCapturedTypesToMembers)

  val smtlibProgram = generateSmtLib(result, resultCapturedTypes, resultCapturedTypesToMembers)
  println(runSmtSolver(smtlibProgram))
}
