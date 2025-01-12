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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.scripts

import java.time.LocalDateTime
import java.time.format.DateTimeFormatter

fun getDateTimeString(
    dSep: Char = '_',
    tSep: Char = '_',
    sep: String = "_",
    millisOfDays: Boolean = true
): String {
  val timeString = if (millisOfDays) "AAAA" else "HH${tSep}mm${tSep}ss"
  return LocalDateTime.now()
      .format(DateTimeFormatter.ofPattern("yyyy${dSep}MM${dSep}dd${sep}$timeString"))
}
