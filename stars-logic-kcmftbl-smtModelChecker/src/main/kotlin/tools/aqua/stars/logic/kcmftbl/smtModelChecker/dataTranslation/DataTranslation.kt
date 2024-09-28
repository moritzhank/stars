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

fun generateSmtLib(
    objRepresentation: MutableList<ObjectRepresentation>,
    capturedTypes: MutableSet<String>,
    capturedTypesToMember: MutableMap<String, MutableMap<String, ObjectReference>>
): String {
  val result = StringBuilder()
  // Generate general datatypes
  result.appendLine("; General datatypes")
  result.appendLine("(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))")
  result.appendLine()
  // Generate sort declarations
  result.appendLine("; Sort declarations")
  for (capturedType in capturedTypes) {
    result.appendLine("(declare-sort $capturedType 0)")
  }
  result.appendLine()
  // Generate member declarations
  result.appendLine("; Member declarations")
  for (capturedType in capturedTypes) {
    result.appendLine("; Member declaration for $capturedType")
    for (entry in capturedTypesToMember[capturedType]!!.entries) {
      val name = entry.component1()
      when (val objRef = entry.component2()) {
        is Enm -> {
          result.appendLine(
              "(declare-fun ${capturedType.firstCharLower()}_$name ($capturedType) Int)")
        }
        is Val<*> -> {
          val primitiveSort = primitiveSmtSort(objRef.value!!).smtSortName
          result.appendLine(
              "(declare-fun ${capturedType.firstCharLower()}_$name ($capturedType) $primitiveSort)")
        }
        is Ref -> {
          val refSort = objRef.ref.getSmtType()!!
          result.appendLine(
              "(declare-fun ${capturedType.firstCharLower()}_$name ($capturedType) $refSort)")
        }
        is Lst<*> -> {
          val primitiveSort = objRef.primitiveSmtSort.smtSortName
          result.appendLine(
              "(declare-fun ${capturedType.firstCharLower()}_$name ($capturedType) (List $primitiveSort))")
        }
        is RefLst -> {
          val refSort = objRef.genericType
          result.appendLine(
              "(declare-fun ${capturedType.firstCharLower()}_$name ($capturedType) (List $refSort))")
        }
        else -> {
          throw IllegalArgumentException("$objRef is no valid ObjectReference.")
        }
      }
    }
  }
  // todo: Generate object representations
  result.appendLine()
  return result.toString()
}

private fun String.firstCharLower(): String = this.replaceFirstChar { it.lowercaseChar() }
