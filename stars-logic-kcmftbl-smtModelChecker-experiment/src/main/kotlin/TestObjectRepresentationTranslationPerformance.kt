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

import kotlin.math.log10
import kotlin.math.pow

// private fun testObjectRepresentationTranslationPerformance(): Pair<Duration, Duration> {
//  val timeSegLoad: Duration?
//  val timeTranslate: Duration?
//  var testSegment: Segment?
//  timeSegLoad = measureTime { testSegment = ExperimentLoader.loadTestSegment() }
//  val result = mutableListOf<ObjectRepresentation>()
//  val resultCapturedTypes = mutableSetOf<String>()
//  val resultCapturedTypesToMembers = mutableMapOf<String, MutableMap<String, ObjectReference>>()
//  timeTranslate = measureTime {
//    testSegment?.toObjectRepresentation(result, resultCapturedTypes, resultCapturedTypesToMembers)
//  }
//  return Pair(timeSegLoad, timeTranslate)
// }
//
// fun main() {
//  val segLoadTimes = mutableListOf<Duration>()
//  val translateTimes = mutableListOf<Duration>()
//  for (i in 0..0) {
//    val testRun = testObjectRepresentationTranslationPerformance()
//    segLoadTimes.add(testRun.component1())
//    translateTimes.add(testRun.component2())
//    SmtTranslatableBase.resetIds()
//  }
//  val timesSegLoadMean = segLoadTimes.map { it.toDouble(DurationUnit.SECONDS) }.mean()
//  val timesTranslationMean = translateTimes.map { it.toDouble(DurationUnit.MILLISECONDS) }.mean()
//  val timesSegLoadGMean = segLoadTimes.map { it.toDouble(DurationUnit.SECONDS) }.gmean()
//  val timesTranslationGMean = translateTimes.map { it.toDouble(DurationUnit.MILLISECONDS)
// }.gmean()
//  val x = FileWriter(File("experiment_times.txt"))
//  x.append(
//      "SegLoad: $segLoadTimes\n" +
//          "Translation: $translateTimes\n" +
//          "Mean SegLoad: ${timesSegLoadMean}s\n" +
//          "Geom. Mean SegLoad: ${timesSegLoadGMean}s\n" +
//          "Mean Translation: ${timesTranslationMean}ms\n" +
//          "Geom. Mean Translation: ${timesTranslationGMean}ms\n")
//  x.close()
// }

private fun Collection<Double>.mean() = sum() / size

private fun Collection<Double>.gmean() = (10.0).pow(fold(0.0) { n, elem -> n + log10(elem) } / size)
