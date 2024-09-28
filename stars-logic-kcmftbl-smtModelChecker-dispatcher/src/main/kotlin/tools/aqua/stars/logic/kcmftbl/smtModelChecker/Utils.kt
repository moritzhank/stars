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

// Copied and modified from https://stackoverflow.com/a/52441962
fun String.runCommand(
    workingDir: File = File("."),
    timeoutAmount: Long = 60,
    timeoutUnit: TimeUnit = TimeUnit.SECONDS
): CommandContext? =
    runCatching {
          val proc =
              ProcessBuilder("\\s".toRegex().split(this))
                  .directory(workingDir)
                  .redirectOutput(ProcessBuilder.Redirect.PIPE)
                  .redirectError(ProcessBuilder.Redirect.PIPE)
                  .start()
                  .also { it.waitFor(timeoutAmount, timeoutUnit) }
          val out = proc.inputStream.bufferedReader().readText()
          val err = proc.errorStream.bufferedReader().readText()
          val exitC = proc.exitValue()
          return CommandContext(out, err, exitC)
        }
        .onFailure { it.printStackTrace() }
        .getOrNull()
