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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.scripts

/** @param outputFile If null the plot will not be saved but displayed on screen */
fun plotPerf(
    outputFile: String?,
    title: String,
    xlabel: String,
    ylabel: String,
    fileName1: String,
    legend1: String,
    scaling1: Float,
    fileName2: String? = null,
    legend2: String? = null,
    scaling2: Float? = null
) {
  val secondPlot = fileName2 != null && legend2 != null && scaling2 != null
  var args =
      arrayOf(
          title, xlabel, ylabel, outputFile ?: "<plot>", fileName1, legend1, scaling1.toString())
  if (secondPlot) {
    requireNotNull(fileName2)
    requireNotNull(legend2)
    requireNotNull(scaling2)
    args = arrayOf(*args, fileName2, legend2, scaling2.toString())
  }
  val proc = PythonCommandLineWrapper.runScript("plotPerf.py", *args)
  if (proc.exitValue() != 0) {
    throw RuntimeException(proc.inputReader().readText() + proc.errorReader().readText())
  }
}
