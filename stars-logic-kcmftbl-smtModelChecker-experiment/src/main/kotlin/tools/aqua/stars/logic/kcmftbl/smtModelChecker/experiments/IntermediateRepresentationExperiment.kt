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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.experiments

import java.io.File
import kotlin.reflect.KClass
import kotlin.time.measureTime
import kotlinx.serialization.modules.EmptySerializersModule
import tools.aqua.stars.data.av.dataclasses.Segment
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.ExperimentLoader
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.SmtIntermediateMember
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.SmtIntermediateRepresentation
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.generateSmtLib
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.getSmtIntermediateRepresentation

fun main() {
  val t: Segment = ExperimentLoader.loadTestSegment()
  println("Finished reading.")
  val serializersModule = EmptySerializersModule()
  val capturedClasses = mutableSetOf<KClass<*>>()
  val capturedLists = mutableListOf<SmtIntermediateMember.List>()
  var intermediateRepresentation: List<SmtIntermediateRepresentation>
  val intermediateRepresentationTime = measureTime {
    intermediateRepresentation =
        getSmtIntermediateRepresentation(serializersModule, t, capturedClasses, capturedLists)
  }
  println("Duration of generation of intermediate representation: $intermediateRepresentationTime")
  println("Size of intermediate representation: ${intermediateRepresentation.size}")
  val smtLib = generateSmtLib(intermediateRepresentation, capturedClasses, capturedLists)
  File("test.smt2").writeText(smtLib)
  println("Generated SmtLib lines: ${smtLib.lines().size}")
  // println("Running solver ...")
  // val ctx = DispatcherTCPContext("127.0.0.1", 7500)
  // val msg = "cvc5\n$smtLib\n\$EOF\$\n"
  // val result = runBlocking { ctx.sendMessage(msg) }
  // println("========[ Result of the solver ]========")
  // println(result)
  // println("========================================")
}
