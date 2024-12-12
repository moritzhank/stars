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

/** Groups IDs of [SmtIntermediateRepresentation] by type/sort */
sealed class SmtDataTranslationWrapper(
    private val intermediateRepresentation: List<SmtIntermediateRepresentation>
) {

  private val capturedKClassesToOccurrence = mutableMapOf<KClass<*>, Int>()
  val externalSmtIDs = Array(intermediateRepresentation.size) { -1 }

  init {
    intermediateRepresentation.forEach { intermediate ->
      val kClass = intermediate::class
      capturedKClassesToOccurrence[kClass] = capturedKClassesToOccurrence.getOrPut(kClass) { 0 } + 1
    }
    //intermediateRepresentation.forEach { intermediate ->

  }
}
