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

@file:Suppress("UndocumentedPublicProperty")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

/** Represents Smt-primitives and their name in SmtLib. */
enum class SmtPrimitive(val smtPrimitiveSortName: String, val defaultValue: Any) {

  BOOL("Bool", false),
  INT("Int", Int.MIN_VALUE),
  REAL("Real", Double.MIN_VALUE),
  STRING("String", "")
}

/** Get [SmtPrimitive] for a [Class] (based on [Class.getSimpleName]). */
fun Class<*>.smtPrimitive(): SmtPrimitive? =
    when (this.simpleName) {
      "boolean" -> SmtPrimitive.BOOL
      "int" -> SmtPrimitive.INT
      "float" -> SmtPrimitive.REAL
      "double" -> SmtPrimitive.REAL
      "String" -> SmtPrimitive.STRING
      else -> null
    }

/** Get [SmtPrimitive] for an object. */
fun Any.smtPrimitive(): SmtPrimitive? =
    when (this) {
      is Boolean -> SmtPrimitive.BOOL
      is Int -> SmtPrimitive.INT
      is Float -> SmtPrimitive.REAL
      is Double -> SmtPrimitive.REAL
      is String -> SmtPrimitive.STRING
      else -> null
    }
