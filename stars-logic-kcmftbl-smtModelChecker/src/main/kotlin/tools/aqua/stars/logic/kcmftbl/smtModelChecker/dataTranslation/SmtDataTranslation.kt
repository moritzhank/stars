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
        val firstTypeArgument = property.firstTypeArgument
        requireNotNull(firstTypeArgument) { TODO() }
        val elementTypeName = firstTypeArgument.smtPrimitive()?.smtPrimitiveSortName ?: firstTypeArgument.simpleName
        result.appendLine("(declare-fun ${sortName.firstCharLower()}_$propName ($sortName) (List $elementTypeName))")
      }
    }
    result.appendLine()
  }
  // Generate declaration of individuals
  result.appendLine("; Declaration of individuals")
  for (intermediate in intermediateRepresentation) {
    val name = "ind_${intermediate.ref.getSmtID()}"
    val sortName = intermediate.ref::class.simpleName!!
    result.appendLine("(declare-const $name $sortName)")
    // Define members
    intermediate.members.keys.forEach { memberName ->
      val propName = "${sortName.firstCharLower()}_$memberName"
      when (val intermediateMember = intermediate.members.getValue(memberName)) {
        is SmtIntermediateMember.Value -> {
          val value = correctFormat(intermediateMember.value)
          result.appendLine("(assert (= ($propName $name) ${value}))")
        }
        is SmtIntermediateMember.Reference -> {
          val refName = "ind_${intermediateMember.refID}"
          result.appendLine("(assert (= ($propName $name) $refName))")
        }
        is SmtIntermediateMember.List -> {
          val listName = "list_${intermediateMember.refID}"
          result.appendLine(";(assert (= ($propName $name) $listName))")
        }
      }
    }
  }
  // Generate lists
  //(assert (= list-car-1 (cons car-123 (cons car-1234 (cons car-12345 nil)))))

  // Generate distinct statement for every sort?!

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

private fun correctFormat(value: Any): Any {
  return when (value) {
    is String -> "\"$value\""
    is Double -> value.toBigDecimal().toPlainString()
    is Float -> value.toBigDecimal().toPlainString()
    else -> value
  }
}
