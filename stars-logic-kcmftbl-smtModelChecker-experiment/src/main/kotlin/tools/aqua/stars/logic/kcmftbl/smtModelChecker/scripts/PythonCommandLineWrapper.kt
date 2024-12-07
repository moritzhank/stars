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

import kotlin.io.path.absolutePathString
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.ExperimentLoader

internal class PythonCommandLineWrapper {

  companion object {

    private var pythonBaseCmdCache: String? = null

    private fun pythonInstalled(name: String): Boolean =
        ProcessBuilder(name, "--version").start().apply { waitFor() }.exitValue() == 0

    private fun pythonBaseCmd(): String {
      val pythonBaseCmdCache = this.pythonBaseCmdCache
      if (pythonBaseCmdCache != null) {
        return pythonBaseCmdCache
      }
      val pythonBaseCmd =
          if (pythonInstalled("python")) {
            "python"
          } else if (pythonInstalled("python3")) {
            "python3"
          } else {
            throw IllegalStateException("No python installation could be found.")
          }
      this.pythonBaseCmdCache = pythonBaseCmd
      return pythonBaseCmd
    }

    fun runScript(name: String, vararg args: String): Process {
      val scriptPath = ExperimentLoader.getPathToResource("/scripts/$name").absolutePathString()
      return ProcessBuilder(pythonBaseCmd(), scriptPath, *args).start().apply { waitFor() }
    }
  }
}
