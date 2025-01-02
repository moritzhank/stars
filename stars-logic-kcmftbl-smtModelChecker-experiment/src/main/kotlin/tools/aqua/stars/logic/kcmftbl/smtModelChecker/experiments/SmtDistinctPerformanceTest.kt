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

@file:Suppress("Unused", "UnusedVariable", "SameParameterValue")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.experiments

import java.io.File
import kotlin.time.Duration
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.SmtSolver
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.getAbsolutePathFromProjectDir
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.runSmtSolver
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.scripts.getDateTimeString
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.scripts.linSpaceArr
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.scripts.plotPerf

private val resultFolderName =
    getAbsolutePathFromProjectDir("experiment${File.separator}smtDistinctPerf")

fun main() {
  File(resultFolderName).mkdirs()

  val rangeOfDistinctStatements = linSpaceArr(2, 3000, 30)
  val rangeOfDistinctStatementsZ3 = linSpaceArr(3000, 10_0000, 30)

  val resultFileCVC5 = runCVC5Experiment(listOf(10, 20, 30), 1)
  // val resultFileZ3 = runZ3Experiment(rangeOfDistinctStatementsZ3, 1)

  val title = "Performance evaluation of SMT solvers for the \'distinct individuals\'-problem"
  plotPerf(
      null,
      title,
      "Number of distinct individuals",
      "Duration [s]",
      resultFileCVC5,
      "CVC5 v1.2.0",
      1 / 1000f)
  File(resultFileCVC5).delete()
}

private fun runZ3Experiment(rangeOfDistinctStatements: List<Int>, repetitions: Int = 3): String {
  return runExperiment(SmtSolver.Z3, rangeOfDistinctStatements, repetitions, "-st") { output ->
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

private fun runCVC5Experiment(rangeOfDistinctStatements: List<Int>, repetitions: Int = 3): String {
  return runExperiment(SmtSolver.CVC5, rangeOfDistinctStatements, repetitions, "--stats") { output
    ->
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

/** @return Path to the resulting CSV file */
private fun runExperiment(
    solver: SmtSolver,
    rangeOfDistinctStatements: List<Int>,
    repetitions: Int,
    vararg solverArgs: String,
    extractDurationFromOutput: (String) -> Duration
): String {
  val results = Array(rangeOfDistinctStatements.size) { Array(repetitions) { -1L } }
  rangeOfDistinctStatements.forEachIndexed { i, numDistinctStatements ->
    val result = runSmtSolver(generateSmtLib(numDistinctStatements), solver, true, *solverArgs)
    (0 ..< repetitions).forEach { j ->
      results[i][j] = extractDurationFromOutput(result).inWholeMilliseconds
      println(
          "${solver.solverName} took ${results[i][j]}ms for $numDistinctStatements distinct-statements (k = $j)")
    }
  }
  // Persist results into csv
  val timeCols = (1..repetitions).fold("") { acc, i -> "$acc\"time$i\", " }.dropLast(2)
  val csv = StringBuilder()
  csv.appendLine("\"numOfDistInd\", $timeCols")
  rangeOfDistinctStatements.forEachIndexed { i, numDistinctStatements ->
    val resultTimeCols =
        (0 ..< repetitions).fold("") { acc, j -> acc + "${results[i][j]}, " }.dropLast(2)
    csv.appendLine("$numDistinctStatements, $resultTimeCols")
  }
  val resultCsvFile =
      File("$resultFolderName${File.separator}${solver.solverName}_${getDateTimeString()}.csv")
  resultCsvFile.writeText(csv.toString())
  return resultCsvFile.absolutePath
}

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
