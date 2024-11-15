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

import tools.aqua.stars.logic.kcmftbl.smtModelChecker.SmtSolver
import kotlin.reflect.KClass

private fun generatePredefinedDatatypes(result: StringBuilder, solver: SmtSolver) {
  result.appendLine("; Predefined datatypes")
  if (solver != SmtSolver.Z3) {
    result.appendLine("(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))")
  }
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

private fun calculateMemberNameToIntermediates(
  intermediateRepresentation: List<SmtIntermediateRepresentation>,
  memberNameToIntermediates: MutableMap<String, SmtDataTranslationIntermediate>
) {
  for (rep in intermediateRepresentation) {
    val repKClass = rep.ref::class
    val annotation = smtTranslationAnnotation(repKClass)
    val sortName = repKClass.simpleName!!
    for (prop in annotation.getTranslatableProperties()) {
      val fullPropName = "${sortName}_${prop.name}"
      val intermediateMember = rep.members.getValue(prop.name)
      memberNameToIntermediates.computeIfAbsent(fullPropName) {
        SmtDataTranslationIntermediate(sortName, SmtIntermediateMemberType.fromMember(intermediateMember), prop.clazz, prop.listTypeArgumentClass)
      }.members.add(Pair(rep.ref.getSmtID(), intermediateMember))
    }
  }
}

private class SmtDataTranslationIntermediate(
  val containerSort: String,
  val memberType: SmtIntermediateMemberType,
  val memberClass: Class<*>,
  val listArgumentClass: Class<*>?,
  val members: MutableList<Pair<Int, SmtIntermediateMember>> = mutableListOf()
)

fun generateSmtLib(
    intermediateRepresentation: List<SmtIntermediateRepresentation>,
    capturedClasses: MutableSet<KClass<*>>,
    capturedLists: MutableList<SmtIntermediateMember.List>,
    solver: SmtSolver = SmtSolver.Z3
): String {
  val result = StringBuilder()
  generatePredefinedDatatypes(result, solver)

  // Generate sort declarations
  result.appendLine("; Sort declarations")
  for (capturedClass in capturedClasses) {
    val sortName = capturedClass.simpleName!!
    result.appendLine("(declare-sort $sortName 0)")
  }
  result.appendLine("(declare-sort ListRef 0)")
  result.appendLine()

  // Generate declaration of all individuals
  result.appendLine("; Declaration of all individuals")
  for (intermediate in intermediateRepresentation) {
    val name = "ind_${intermediate.ref.getSmtID()}"
    val sortName = intermediate.ref::class.simpleName!!
    result.appendLine("(declare-const $name $sortName)")
  }
  result.appendLine()

  // Generate declaration of all lists
  result.appendLine("; Declaration of all lists")
  for (capturedList in capturedLists) {
    val name = "list_${capturedList.refID}"
    result.appendLine("(declare-const $name ListRef)")
  }
  result.appendLine()


  // TODO: Is this necessary? This is a real performance hit for smt-solvers.
  // Generate distinct statement for every sort and their individuals
  /*
  result.appendLine("; Distinct statements for all sorts and their individuals")
  for (sortKClass in capturedClasses) {
    val intermediates = intermediateRepresentation.filter { it.ref::class == sortKClass }
    val listOfIndividuals = intermediates.fold(StringBuilder()) { str, elem -> str.append("ind_${elem.ref.getSmtID()} ") }
    result.appendLine("(assert (distinct ${listOfIndividuals.toString().dropLast(1)}))")
  }
  result.appendLine()
  // TODO: If necessary, also to be generated for ListRef
   */

  // Generate member definitions
  result.appendLine("; Member definitions")
  val memberNameToIntermediates = mutableMapOf<String, SmtDataTranslationIntermediate>()
  calculateMemberNameToIntermediates(intermediateRepresentation, memberNameToIntermediates)
  for (memberName in memberNameToIntermediates.keys) {
    val intermediate = memberNameToIntermediates.getValue(memberName)
    require(intermediate.members.size > 0) { "There cannot be an empty list of members." }
    when(intermediate.memberType) {
      // Calculate member definition for values
      SmtIntermediateMemberType.VALUE -> {
        var iteStructureFront = StringBuilder("")
        var bracketsNeeded = 0
        intermediate.members.forEachIndexed { index, pair ->
          // Skip first index
          if(index != 0) {
            val memberSmtID = pair.first
            val member = pair.second as SmtIntermediateMember.Value
            val ifIndName = "ind_$memberSmtID"
            val thenValue = "${correctFormat(member.value)}"
            iteStructureFront.append("(ite (= x $ifIndName) $thenValue ")
            bracketsNeeded++
          }
        }
        val firstVal = correctFormat((intermediate.members.first().second as SmtIntermediateMember.Value).value)
        iteStructureFront.append("$firstVal${")".repeat(bracketsNeeded)}")
        val returnSort = intermediate.memberClass.smtPrimitive()!!.smtPrimitiveSortName
        result.appendLine("(define-fun $memberName ((x ${intermediate.containerSort})) $returnSort $iteStructureFront)")
      }
      // Calculate member definition for references
      SmtIntermediateMemberType.REFERENCE -> {
        var iteStructureFront = StringBuilder("")
        var bracketsNeeded = 0
        intermediate.members.forEachIndexed { index, pair ->
          // Skip first index
          if(index != 0) {
            val memberSmtID = pair.first
            val member = pair.second as SmtIntermediateMember.Reference
            val ifIndName = "ind_$memberSmtID"
            val then = "ind_${member.refID}"
            iteStructureFront.append("(ite (= x $ifIndName) $then ")
            bracketsNeeded++
          }
        }
        val firstVal = "ind_${(intermediate.members.first().second as SmtIntermediateMember.Reference).refID}"
        iteStructureFront.append("$firstVal${")".repeat(bracketsNeeded)}")
        val returnSort = intermediate.memberClass.simpleName
        result.appendLine("(define-fun $memberName ((x ${intermediate.containerSort})) $returnSort $iteStructureFront)")
      }
      // Calculate member definition for lists
      // TODO: Generate propName_isListElement(list, elem)
      SmtIntermediateMemberType.VALUE_LIST, SmtIntermediateMemberType.REFERENCE_LIST -> {
        // Generate ListRef mapping
        var iteStructureFront = StringBuilder("")
        var bracketsNeeded = 0
        intermediate.members.forEachIndexed { index, pair ->
          // Skip first index
          if(index != 0) {
            val memberSmtID = pair.first
            val member = pair.second as SmtIntermediateMember.List
            val ifIndName = "ind_$memberSmtID"
            val then = "list_${member.refID}"
            iteStructureFront.append("(ite (= x $ifIndName) $then ")
            bracketsNeeded++
          }
        }
        val firstVal = "list_${(intermediate.members.first().second as SmtIntermediateMember.List).refID}"
        iteStructureFront.append("$firstVal${")".repeat(bracketsNeeded)}")
        result.appendLine("(define-fun $memberName ((x ${intermediate.containerSort})) ListRef $iteStructureFront)")
        // Generate isListElement function
        // TODO: ITE für jede mögliche ListREF
          // TODO: ITE für jedes mögliche Element
        // TODO
        val listArgumentClass = intermediate.listArgumentClass!!
        val listArgumentSort = listArgumentClass.smtPrimitive()?.smtPrimitiveSortName ?: listArgumentClass.simpleName
        result.appendLine(";(define-fun ${memberName}_isElement ((x ListRef) (y $listArgumentSort)) Bool [ITE])")
      }
    }
  }

  result.appendLine()
  result.appendLine("(check-sat)")
  return result.toString()
}
