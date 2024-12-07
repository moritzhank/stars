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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc

import java.io.File
import java.nio.file.Paths
import kotlin.io.path.absolutePathString

/** Returns the absolute path of [path] from the project dir, guaranteed without '\' or '/' at the end */
fun getAbsolutePathFromProjectDir(path: String) =
    Paths.get("${Paths.get("").absolutePathString()}${File.separator}$path").absolutePathString().dropLastWhile {
      it == File.separatorChar
    }
