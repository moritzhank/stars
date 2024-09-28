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

import java.io.File
import java.io.FileWriter
import kotlin.math.log10
import kotlin.math.pow
import kotlin.time.Duration
import kotlin.time.DurationUnit
import kotlin.time.measureTime
import tools.aqua.stars.data.av.dataclasses.Segment
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.ObjectReference
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.ObjectRepresentation
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.SmtTranslatable
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.generateSmtLib

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

fun main() {
  val timesSegLoad = mutableListOf<Duration>()
  val timesTranslation = mutableListOf<Duration>()
  for (i in 0..99) {
    var testSegment: Segment?
    var time = measureTime { testSegment = ExperimentLoader.loadTestSegment() }
    timesSegLoad.add(time)
    val result = mutableListOf<ObjectRepresentation>()
    val resultCapturedTypes = mutableSetOf<String>()
    val resultCapturedTypesToMembers = mutableMapOf<String, MutableMap<String, ObjectReference>>()
    time = measureTime {
      testSegment?.toObjectRepresentation(result, resultCapturedTypes, resultCapturedTypesToMembers)
    }
    timesTranslation.add(time)

    // Generate SMTLIB
    //val smtlib = generateSmtLib(result, resultCapturedTypes, resultCapturedTypesToMembers)
    //println(smtlib)

    SmtTranslatable.resetIds()
  }
  val timesSegLoadMean = timesSegLoad.map { it.toDouble(DurationUnit.SECONDS) }.mean()
  val timesTranslationMean = timesTranslation.map { it.toDouble(DurationUnit.MILLISECONDS) }.mean()
  var timesSegLoadGMean = timesSegLoad.map { it.toDouble(DurationUnit.SECONDS) }.gmean()
  val timesTranslationGMean =
      timesTranslation.map { it.toDouble(DurationUnit.MILLISECONDS) }.gmean()
  val x = FileWriter(File("experiment_times.txt"))
  x.append(
      "SegLoad: $timesSegLoad\n" +
          "Translation: $timesTranslation\n" +
          "Mean SegLoad: ${timesSegLoadMean}s\n" +
          "Geom. Mean SegLoad: ${timesSegLoadGMean}s\n" +
          "Mean Translation: ${timesTranslationMean}ms\n" +
          "Geom. Mean Translation: ${timesTranslationGMean}ms\n")
  x.close()
}

fun Collection<Double>.mean() = sum() / size

fun Collection<Double>.gmean() = (10.0).pow(fold(0.0) { n, elem -> n + log10(elem) } / size)
