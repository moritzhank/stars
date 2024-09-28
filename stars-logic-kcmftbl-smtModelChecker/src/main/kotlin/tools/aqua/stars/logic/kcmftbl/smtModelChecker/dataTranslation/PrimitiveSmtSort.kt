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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

enum class PrimitiveSmtSort(val smtSortName: String) {

  BOOL("Bool"),
  INT("Int"),
  REAL("Real"),
  STRING("String")
}

fun primitiveSmtSort(obj: Any): PrimitiveSmtSort {
  val simpleName = obj::class.simpleName
  val result =
      when (simpleName) {
        "Boolean" -> PrimitiveSmtSort.BOOL
        "Int" -> PrimitiveSmtSort.INT
        "Float" -> PrimitiveSmtSort.REAL
        "Double" -> PrimitiveSmtSort.REAL
        "String" -> PrimitiveSmtSort.STRING
        else -> null
      }
  requireNotNull(result) { "$obj has no primitive smt-type." }
  return result
}
