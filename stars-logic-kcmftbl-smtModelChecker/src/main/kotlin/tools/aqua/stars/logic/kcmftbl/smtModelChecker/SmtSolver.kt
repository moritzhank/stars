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

@file:Suppress("unused")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker

import java.io.File
import java.util.UUID
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.getAbsolutePathFromProjectDir

enum class SmtSolver(val solverName: String) {
  CVC5("cvc5"),
  Z3("z3")
}

fun runSmtSolver(
    program: String,
    solver: SmtSolver = SmtSolver.CVC5,
    removeSmt2File: Boolean = true,
    vararg solverArgs: String
): String {
  val settings = SmtSolverSettings.load()
  requireNotNull(settings) {
    SmtSolverSettings.generateTemplate()
    "The file smtSolverSettings.json must be specified."
  }
  val solverBinPath = settings.getPathToSolverBin(solver)
  require(File(solverBinPath).exists()) {
    "The specified binary (at \"$solverBinPath\") for ${solver.solverName} does not exist."
  }
  val smtTmpDirPath = getAbsolutePathFromProjectDir("smtTmp")
  File(smtTmpDirPath).mkdir()
  val smt2FilePath = "$smtTmpDirPath${File.separator}${UUID.randomUUID()}.smt2"
  val smt2File = File(smt2FilePath).apply { writeText(program) }
  val proc = ProcessBuilder(solverBinPath, smt2FilePath, *solverArgs).start().apply { waitFor() }
  val result = proc.inputReader().readText() + proc.errorReader().readText()
  if (removeSmt2File) {
    smt2File.delete()
  }
  return result
}
