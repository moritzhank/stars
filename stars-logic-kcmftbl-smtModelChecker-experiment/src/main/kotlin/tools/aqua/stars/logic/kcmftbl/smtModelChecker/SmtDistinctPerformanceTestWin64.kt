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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker

import java.io.File
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import kotlin.io.path.absolutePathString
import kotlin.time.Duration

const val VERBOSE = true

fun main() {
  val rangeOfDistinctStatements =
      arrayOf(
          2,
          105,
          208,
          312,
          415,
          518,
          622,
          725,
          829,
          932,
          1035,
          1139,
          1242,
          1345,
          1449,
          1552,
          1656,
          1759,
          1862,
          1966,
          2069,
          2172,
          2276,
          2379,
          2483,
          2586,
          2689,
          2793,
          2896,
          3000)
  val rangeOfDistinctStatementsZ3 =
      arrayOf(
          3000,
          6344,
          9689,
          13034,
          16379,
          19724,
          23068,
          26413,
          29758,
          33103,
          36448,
          39793,
          43137,
          46482,
          49827,
          53172,
          56517,
          59862,
          63206,
          66551,
          69896,
          73241,
          76586,
          79931,
          83275,
          86620,
          89965,
          93310,
          96655,
          100000)
  // val resultFileCVC5 = runCVC5Experiment(rangeOfDistinctStatements)
  // val resultFileZ3 = runZ3Experiment(rangeOfDistinctStatementsZ3, 1)

  val fileCVC5 =
      "C:\\Users\\hanek\\Desktop\\stars\\smtDistinctPerfTestWin64\\result_cvc5_2024_12_04__20_52.csv"
  val fileZ3 =
      "C:\\Users\\hanek\\Desktop\\stars\\smtDistinctPerfTestWin64\\result_z3_2024_12_04__21_12.csv"
  val title = "Performance evaluation of SMT solvers for the \'distinct individuals\'-problem"
  callPlotScript(
      title,
      "Number of distinct individuals",
      "Duration [s]",
      fileZ3,
      "Z3 v4.13.3 (mean of 3x runs)",
      1 / 1000f,
      fileCVC5,
      "CVC5 v1.2.0 (mean of 3x runs)",
      1 / 1000f)

  /*
  val title = "Performance evaluation of SMT solvers for the \'distinct individuals\'-problem"
  callPlotScript(title, "Number of distinct individuals", "Duration [s]", resultFileZ3, "Z3 v4.13.3", 1/1000f)
   */
}

private fun callPlotScript(
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
  val saveFile = File("smtDistinctPerfTestWin64/plot_${getDateTimeString()}.png").absolutePath
  var args = arrayOf(title, xlabel, ylabel, saveFile, fileName1, legend1, scaling1.toString())
  if (secondPlot) {
    requireNotNull(fileName2)
    requireNotNull(legend2)
    requireNotNull(scaling2)
    args = arrayOf(*args, fileName2, legend2, scaling2.toString())
  }
  val proc =
      ProcessBuilder(
              "python",
              ExperimentLoader.getPathToResource("/scripts/plotPerf.py").absolutePathString(),
              *args)
          .start()
          .apply { waitFor() }
  if (VERBOSE) {
    print(proc.inputReader().readText())
    print(proc.errorReader().readText())
  }
}

private fun runZ3Experiment(rangeOfDistinctStatements: Array<Int>, repetitions: Int = 3): String {
  val pathToZ3Bin = "C:\\Users\\hanek\\Desktop\\z3-4.13.3-x64-win\\bin\\z3.exe"
  return runExperiment(pathToZ3Bin, "z3", rangeOfDistinctStatements, repetitions, "-st") { output ->
    val prefix = " :total-time"
    output.lines().forEachIndexed { i, line ->
      if (i == 0) {
        require(line == "sat")
      } else if (line.startsWith(prefix)) {
        return@runExperiment Duration.parse(
            line.drop(prefix.length).dropLast(1).replace(" ", "") + "s")
      }
    }
    throw IllegalArgumentException()
  }
}

private fun runCVC5Experiment(rangeOfDistinctStatements: Array<Int>, repetitions: Int = 3): String {
  val pathToCVC5Bin = "C:\\Users\\hanek\\Desktop\\cvc5-Win64-x86_64-shared\\bin\\cvc5.exe"
  return runExperiment(pathToCVC5Bin, "cvc5", rangeOfDistinctStatements, repetitions, "--stats") {
      output ->
    val prefix = "global::totalTime = "
    output.lines().forEachIndexed { i, line ->
      if (i == 0) {
        require(line == "sat")
      } else if (line.startsWith(prefix)) {
        return@runExperiment Duration.parse(line.drop(prefix.length))
      }
    }
    throw IllegalArgumentException()
  }
}

private fun runExperiment(
    absPathToSolverBin: String,
    solverName: String,
    rangeOfDistinctStatements: Array<Int>,
    repetitions: Int,
    vararg commands: String,
    extractDurationFromOutput: (String) -> Duration
): String {
  val resultFolderName = "smtDistinctPerfTestWin64"
  File(resultFolderName).mkdirs()
  val results = Array(rangeOfDistinctStatements.size) { Array(repetitions) { -1L } }
  val currentSmt2File = File("$resultFolderName\\current.smt2")
  rangeOfDistinctStatements.forEachIndexed { i, numDistinctStatements ->
    currentSmt2File.writeText(generateSmtLib(numDistinctStatements))
    (0 ..< repetitions).forEach { j ->
      val proc =
          ProcessBuilder(absPathToSolverBin, currentSmt2File.absolutePath, *commands)
              .redirectOutput(ProcessBuilder.Redirect.PIPE)
              .start()
              .apply { waitFor() }
      val procResult = proc.inputReader().readText() + proc.errorReader().readText()
      results[i][j] = extractDurationFromOutput(procResult).inWholeMilliseconds
      if (VERBOSE) {
        println(
            "$solverName took ${results[i][j]}ms for $numDistinctStatements distinct-statements (k = $j)")
      }
    }
  }
  currentSmt2File.delete()
  // Persist results into csv
  val timeCols = (1..repetitions).fold("") { acc, i -> "$acc\"time$i\", " }.dropLast(2)
  val csv = StringBuilder()
  csv.appendLine("\"numOfDistInd\", $timeCols")
  rangeOfDistinctStatements.forEachIndexed { i, numDistinctStatements ->
    val resultTimeCols =
        (0 ..< repetitions).fold("") { acc, j -> acc + "${results[i][j]}, " }.dropLast(2)
    csv.appendLine("$numDistinctStatements, $resultTimeCols")
  }
  val resultCsvFile = File("$resultFolderName\\result_${solverName}_${getDateTimeString()}.csv")
  resultCsvFile.writeText(csv.toString())
  return resultCsvFile.absolutePath
}

private fun getDateTimeString() =
    LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy_MM_dd__HH_mm"))

private fun generateSmtLib(numDistinctStatements: Int): String {
  val result = StringBuilder()
  result.appendLine("(set-logic ALL)")
  result.appendLine("(declare-sort TestSort 0)")
  for (i in 1..numDistinctStatements) {
    result.appendLine("(declare-const ind_$i TestSort)")
  }
  result.append("(assert (distinct ")
  for (i in 1..numDistinctStatements) {
    result.append("ind_$i ")
  }
  result.appendLine("))")
  result.appendLine("(check-sat)")
  return result.toString()
}
