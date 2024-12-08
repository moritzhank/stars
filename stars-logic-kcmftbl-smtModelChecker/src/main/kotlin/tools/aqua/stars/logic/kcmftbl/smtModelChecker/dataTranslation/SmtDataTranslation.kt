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

@file:Suppress("StringLiteralDuplication", "UseDataClass")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

import kotlin.reflect.KClass
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.SmtSolver
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.firstCharLower
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.toSmtLibPrimitiveFormat

/** Captures information about a member needed for translation. */
private class SmtDataTranslationIntermediate(
    /** Sort of the object that contains the member represented by this class. */
    val containerSort: String,
    val memberType: SmtIntermediateMemberType,
    /** Type of the member represented by this class. */
    val memberClass: Class<*>,
    val listArgumentClass: Class<*>?,
    /**
     * The Pair contains the id of the individual that has the member (Represented by this class)
     * and the corresponding implementation (SmtIntermediateMember).
     */
    val members: MutableList<Pair<Int, SmtIntermediateMember>> = mutableListOf()
)

/** Generate SmtLib. */
fun generateSmtLib(
    intermediateRepresentation: List<SmtIntermediateRepresentation>,
    capturedClasses: MutableSet<KClass<*>>,
    capturedLists: MutableList<SmtIntermediateMember.List>,
    solver: SmtSolver = SmtSolver.CVC5
): String {
  val result = StringBuilder()
  if (solver == SmtSolver.CVC5) {
    result.appendLine("(set-logic ALL)")
    result.appendLine()
  }
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

  // TODO: These are necessary but they are a heavy performance hit
  // Generate distinct statement for every sort and their individuals
  result.appendLine("; Distinct statements for all sorts and their individuals")
  for (sortKClass in capturedClasses) {
    val intermediates = intermediateRepresentation.filter { it.ref::class == sortKClass }
    if (intermediates.size <= 1) {
      continue
    }
    val listOfIndividuals =
        intermediates.fold(StringBuilder()) { str, elem ->
          str.append("ind_${elem.ref.getSmtID()} ")
        }
    result.appendLine("(assert (distinct ${listOfIndividuals.toString().dropLast(1)}))")
  }
  // Generate distinct statements for every ListRef-object
  if (capturedLists.size > 1) {
    val listOfListRefs =
        capturedLists.fold(StringBuilder()) { str, elem -> str.append("list_${elem.refID} ") }
    result.appendLine("(assert (distinct ${listOfListRefs.toString().dropLast(1)}))")
  }
  result.appendLine()

  // Generate member definitions
  result.appendLine("; Member definitions")
  val memberNameToIntermediates = mutableMapOf<String, SmtDataTranslationIntermediate>()
  calculateMemberNameToIntermediates(intermediateRepresentation, memberNameToIntermediates)
  for (memberName in memberNameToIntermediates.keys) {
    val intermediate = memberNameToIntermediates.getValue(memberName)
    require(intermediate.members.isNotEmpty()) { "There cannot be an empty list of members." }
    when (intermediate.memberType) {
      // Calculate member definition for values
      SmtIntermediateMemberType.VALUE -> {
        val iteStructure =
            generateITEStructure(
                intermediate.members,
                "x",
                { ifPair -> "ind_${ifPair.first}" },
                { thenPair ->
                  (thenPair.second as SmtIntermediateMember.Value).value.toSmtLibPrimitiveFormat()
                })
        val returnSort = intermediate.memberClass.smtPrimitive()!!.smtPrimitiveSortName
        result.appendLine(
            "(define-fun ${memberName.firstCharLower()} ((x ${intermediate.containerSort})) $returnSort $iteStructure)")
      }
      // Calculate member definition for references
      SmtIntermediateMemberType.REFERENCE -> {
        val iteStructure =
            generateITEStructure(
                intermediate.members,
                "x",
                { ifPair -> "ind_${ifPair.first}" },
                { thenPair -> "ind_${(thenPair.second as SmtIntermediateMember.Reference).refID}" })
        val returnSort = intermediate.memberClass.simpleName
        result.appendLine(
            "(define-fun ${memberName.firstCharLower()} ((x ${intermediate.containerSort})) $returnSort $iteStructure)")
      }
      // Calculate member definition for lists
      SmtIntermediateMemberType.VALUE_LIST,
      SmtIntermediateMemberType.REFERENCE_LIST -> {
        // Generate ListRef mapping
        val iteStructure =
            generateITEStructure(
                intermediate.members,
                "x",
                { ifPair -> "ind_${ifPair.first}" },
                { thenPair -> "list_${(thenPair.second as SmtIntermediateMember.List).refID}" })
        result.appendLine(
            "(define-fun ${memberName.firstCharLower()} ((x ${intermediate.containerSort})) ListRef $iteStructure)")
        // Generate isListElement function
        val listArgumentClass = intermediate.listArgumentClass!!
        val listArgumentSort =
            listArgumentClass.smtPrimitive()?.smtPrimitiveSortName ?: listArgumentClass.simpleName
        // The outer ite structure contains ites over all possible ListRef objects. The inner ite
        // structure contains ite over all possible elements of the corresponding listRef.
        val outerITEStructure =
            generateITEStructure(
                intermediate.members,
                "x",
                { ifPair -> "list_${(ifPair.second as SmtIntermediateMember.List).refID}" },
                { thenPair ->
                  when (val member = thenPair.second as SmtIntermediateMember.List) {
                    is SmtIntermediateMember.List.ValueList -> {
                      TODO()
                    }
                    is SmtIntermediateMember.List.ReferenceList -> {
                      val refList = member.list
                      if (!refList.isEmpty()) {
                        generateITEStructure(
                            refList, "y", { ifElem -> "ind_${ifElem}" }, { _ -> "true" }, "false")
                      } else {
                        // An empty list has no elements
                        // TODO: Maybe implement possibility to omit these entries
                        "false"
                      }
                    }
                  }
                },
                "false")
        result.appendLine(
            "(define-fun ${memberName.firstCharLower()}_isListElement ((x ListRef) (y $listArgumentSort)) Bool $outerITEStructure)")
      }
    }
  }
  result.appendLine()

  result.appendLine("(check-sat)")
  return result.toString()
}

private fun generatePredefinedDatatypes(result: StringBuilder, solver: SmtSolver) {
  result.appendLine("; Predefined datatypes")
  if (solver != SmtSolver.Z3) {
    result.appendLine("(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))")
  }
  result.appendLine()
}

private fun calculateMemberNameToIntermediates(
    intermediateRepresentation: List<SmtIntermediateRepresentation>,
    memberNameToIntermediates: MutableMap<String, SmtDataTranslationIntermediate>
) {
  for (rep in intermediateRepresentation) {
    val repKClass = rep.ref::class
    val annotation = smtTranslationClassInfo(repKClass)
    val sortName = repKClass.simpleName!!
    for (prop in annotation.getTranslatableProperties()) {
      val fullPropName = "${sortName}_${prop.name}"
      val intermediateMember = rep.members.getValue(prop.name)
      memberNameToIntermediates
          .computeIfAbsent(fullPropName) {
            SmtDataTranslationIntermediate(
                sortName, intermediateMember.type(), prop.clazz, prop.listTypeArgumentClass)
          }
          .members
          .add(Pair(rep.ref.getSmtID(), intermediateMember))
    }
  }
}

private fun <T> generateITEStructure(
    list: Collection<T>,
    varName: String,
    ifStr: (T) -> String,
    thenStr: (T) -> String,
    defaultValue: String? = null
): String {
  val iteStructureFront = StringBuilder("")
  var bracketsNeeded = 0
  val firstElem = list.first()
  list.forEachIndexed { index, elem ->
    // Skip first element if no default is given
    val skip = defaultValue == null && index == 0
    if (!skip) {
      iteStructureFront.append("(ite (= $varName ${ifStr(elem)}) ${thenStr(elem)} ")
      bracketsNeeded++
    }
  }
  if (defaultValue == null) {
    iteStructureFront.append("${thenStr(firstElem)}${")".repeat(bracketsNeeded)}")
  } else {
    iteStructureFront.append("$defaultValue${")".repeat(bracketsNeeded)}")
  }
  return iteStructureFront.toString()
}
