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

@file:Suppress("unused", "ClassOrdering")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

/** Ensures that each object has a unique ID. */
abstract class SmtTranslatableBase {

  companion object {

    private var nextSmtId = 0

    internal fun uniqueSmtID() = nextSmtId++
  }

  private var _smtID: Int? = null

  internal fun getSmtID(): Int {
    var smtID = _smtID
    if (smtID == null) {
      smtID = uniqueSmtID()
      _smtID = smtID
    }
    return smtID
  }

  internal fun getSmtTranslationClassInfo(): SmtTranslationClassInfo =
      smtTranslationClassInfo(this::class)
}
