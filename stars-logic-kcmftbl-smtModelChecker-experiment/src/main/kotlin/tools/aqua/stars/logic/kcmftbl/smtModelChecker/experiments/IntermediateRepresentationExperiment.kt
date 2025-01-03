/*
 * Copyright 2024-2025 The STARS Project Authors
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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.experiments

import kotlin.time.measureTime
import kotlinx.serialization.modules.EmptySerializersModule
import tools.aqua.stars.data.av.dataclasses.Segment
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.ExperimentLoader
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.SmtSolver
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.SmtDataTranslationWrapper
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.SmtIntermediateRepresentation
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.generateSmtLib
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.getSmtIntermediateRepresentation
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.runSmtSolver

fun main() {
  // Options
  val solver = SmtSolver.CVC5
  val removeSmt2File = false

  val t: Segment = ExperimentLoader.loadTestSegment()
  println("Finished reading.")
  val serializersModule = EmptySerializersModule()
  var intermediateRepresentation: List<SmtIntermediateRepresentation>
  val intermediateRepresentationTime = measureTime {
    intermediateRepresentation = getSmtIntermediateRepresentation(serializersModule, t)
  }
  println("Duration of generation of intermediate representation: $intermediateRepresentationTime")
  println("Size of intermediate representation: ${intermediateRepresentation.size}")
  var translationWrapper: SmtDataTranslationWrapper
  val translationWrapperTime = measureTime {
    translationWrapper = SmtDataTranslationWrapper(intermediateRepresentation)
  }
  println("Duration of generation of SmtDataTranslationWrapper: $translationWrapperTime")
  var smtLib: String
  val smtLibTime = measureTime { smtLib = generateSmtLib(translationWrapper) }
  smtLib += "(check-sat)"
  println("Duration of generation of SMT-LIB: $smtLibTime")
  println("Generated SmtLib lines: ${smtLib.lines().size}")
  val statsOption = if (solver == SmtSolver.Z3) "-st" else "--stats"
  println("Running solver ...")
  println("========[ Result of the solver ]========")
  println(runSmtSolver(smtLib, solver, removeSmt2File, statsOption))
  println("========================================")
}
