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

import kotlin.reflect.KClass

fun generateSmtLib(
    intermediateRepresentation: List<SmtIntermediateRepresentation>,
    capturedClasses: MutableSet<KClass<*>>
): String {
  val result = StringBuilder()
  generatePredefinedDatatypes(result)
  // Generate sort declarations
  result.appendLine("; Sort declarations")
  for (capturedClass in capturedClasses) {
    val annotation = smtTranslationAnnotation(capturedClass)
    val sortName = capturedClass.simpleName!!
    result.appendLine("(declare-sort $sortName 0)")
  }
  result.appendLine()
  // Generate member declarations
  for (capturedClass in capturedClasses) {
    val annotation = smtTranslationAnnotation(capturedClass)
    val sortName = capturedClass.simpleName!!
    result.appendLine("; Member declarations for $sortName")
    for (property in annotation.getLegalProperties()) {
      val propName = property.name
      // property.clazz is null for all parameterised classes
      if (property.clazz != null) {
        val smtPrimitive = property.clazz.smtPrimitive()
        // smtPrimitive is null for all non-primitive classes
        if (smtPrimitive != null) {
          result.appendLine(
              "(declare-fun ${sortName.firstCharLower()}_$propName ($sortName) ${smtPrimitive.smtPrimitiveSortName})")
        } else {
          val returnSortName = property.clazz.simpleName
          result.appendLine(
              "(declare-fun ${sortName.firstCharLower()}_$propName ($sortName) $returnSortName)")
        }
      } else {
        result.appendLine(";[parameterized] $propName")
        // TODO
      }

      //
      //      when (val objRef = entry.component2()) {
      //        is Val<*> -> {
      //          val primitiveSort = primitiveSmtSort(objRef.value!!).smtSortName
      //
      //        }
      //        is Ref -> {
      //          val refSort = objRef.ref.getSmtType()!!
      //          result.appendLine(
      //            "(declare-fun ${capturedType.firstCharLower()}_$name ($capturedType) $refSort)")
      //        }
      //        is Lst<*> -> {
      //          val primitiveSort = objRef.primitiveSmtSort.smtSortName
      //          result.appendLine(
      //            "(declare-fun ${capturedType.firstCharLower()}_$name ($capturedType) (List
      //            $primitiveSort))")
      //        }
      //        is RefLst -> {
      //          val refSort = objRef.genericType
      //          result.appendLine(
      //            "(declare-fun ${capturedType.firstCharLower()}_$name ($capturedType) (List
      //            $refSort))")
      //        }
      //        else -> {
      //          throw IllegalArgumentException("$objRef is no valid ObjectReference.")
      //        }
      //      }
    }

    result.appendLine()
  }
  // Generate declaration of individuals
  result.appendLine("; Declaration of individuals")
  for (intermediate in intermediateRepresentation) {
    val name = "ind_${intermediate.ref.getSmtID()}"
    val sortName = intermediate.ref::class.simpleName!!
    result.appendLine("(declare-const $name $sortName)")
  }
  result.appendLine()
  result.appendLine("(check-sat)")
  return result.toString()
}

private fun generatePredefinedDatatypes(result: StringBuilder) {
  result.appendLine("; Predefined datatypes")
  result.appendLine("(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))")
  result.appendLine()
}

private fun String.firstCharLower(): String = this.replaceFirstChar { it.lowercaseChar() }
