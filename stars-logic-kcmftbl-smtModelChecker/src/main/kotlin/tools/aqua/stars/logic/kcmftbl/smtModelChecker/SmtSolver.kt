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
import java.util.UUID
import java.util.concurrent.TimeUnit
import tools.aqua.stars.logic.kcmftbl.dsl.FormulaBuilder

fun main() {
  val program = "(echo \"test\")"
  println(runSmtSolver(program, SmtSolver.Z3))
}

enum class SmtSolver(val solverName: String) {
  CVC5("cvc5"),
  Z3("z3")
}

fun tryRunSmtSolver(program: String, solver: SmtSolver = SmtSolver.CVC5): String? {
  return try {
    runSmtSolver(program, solver)
  } catch (e: Exception) {
    null
  }
}

fun runSmtSolver(program: String, solver: SmtSolver = SmtSolver.CVC5): String {
  val dockerFileName = "/Dockerfile"
  val workDir =
      FormulaBuilder::class.java.getResource(dockerFileName)?.path!!.dropLast(dockerFileName.length)
  val solverName = solver.solverName
  val generatedFileName = "run-${UUID.randomUUID()}.txt"
  val generatedFilePath = "$workDir/exchange/$generatedFileName"
  val generatedFile = File(generatedFilePath)
  generatedFile.writeText(program)
  val run =
      "docker run --rm --mount type=bind,source=$workDir/exchange,target=/root/exchange smt-solver $solverName $generatedFileName".runCommand(
          File(workDir))
  generatedFile.delete()
  checkNotNull(run) { "Error running the Docker container." }
  return run
}

// Copied from: https://stackoverflow.com/a/41495542 and modified
private fun String.runCommand(workingDir: File, timeOutInMS: Long = 60 * 60 * 1000): String? {
  try {
    val parts = this.split("\\s".toRegex())
    val proc =
        ProcessBuilder(*parts.toTypedArray())
            .directory(workingDir)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start()
    proc.waitFor(timeOutInMS, TimeUnit.MILLISECONDS)
    if (proc.exitValue() != 0)
        throw IllegalStateException(
            "Error executing a command:${System.lineSeparator()}${proc.errorStream.bufferedReader().readText()}")
    return proc.inputStream.bufferedReader().readText()
  } catch (e: Exception) {
    e.printStackTrace()
    return null
  }
}
