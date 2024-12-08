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

@file:Suppress("ExpressionBodySyntax")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc

/** Replaces first character with a lower-case one. */
fun String.firstCharLower(): String = this.replaceFirstChar { it.lowercaseChar() }

/** Converts given primitive to SmtLib format. */
fun Any.toSmtLibPrimitiveFormat(): String {
  return when (this) {
    is String -> "\"$this\""
    is Double -> this.toBigDecimal().toPlainString()
    is Float -> this.toBigDecimal().toPlainString()
    else -> this.toString()
  }
}
