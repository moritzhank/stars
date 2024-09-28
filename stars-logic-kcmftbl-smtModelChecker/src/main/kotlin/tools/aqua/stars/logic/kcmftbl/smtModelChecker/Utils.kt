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
import java.util.concurrent.TimeUnit

// Copied from: https://stackoverflow.com/a/41495542 and modified
fun String.runCommand(workingDir: File, timeOutInMS: Long = 60 * 60 * 1000): String? {
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
