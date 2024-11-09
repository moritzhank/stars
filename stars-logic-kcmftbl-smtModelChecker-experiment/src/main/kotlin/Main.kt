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

import kotlin.reflect.KClass
import kotlin.time.measureTime
import kotlinx.serialization.modules.EmptySerializersModule
import tools.aqua.stars.data.av.dataclasses.Segment
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.SmtIntermediateRepresentation
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.generateSmtLib
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.getSmtIntermediateRepresentation
import java.io.FileWriter

fun main() {
  val t: Segment = ExperimentLoader.loadTestSegment()
  println("Finished reading.")
  val serializersModule = EmptySerializersModule()
  val capturedClasses = mutableSetOf<KClass<*>>()
  var intermediateRepresentation: List<SmtIntermediateRepresentation> = listOf()
  val intermediateRepresentationTime = measureTime {
    intermediateRepresentation =
      getSmtIntermediateRepresentation(serializersModule, t, capturedClasses)
  }
  println("Duration of generation of intermediate representation: $intermediateRepresentationTime")
  println("Size of intermediate representation: ${intermediateRepresentation.size}")
  val smtLib = generateSmtLib(intermediateRepresentation, capturedClasses)
  println("Generated SmtLib lines: ${smtLib.length}")
  FileWriter("test.txt").write(smtLib)
}
