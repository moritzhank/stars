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
import kotlinx.metadata.isNotDefault
import kotlinx.metadata.jvm.KotlinClassMetadata

internal val SMT_TRANSLATION_CACHE = ClassValueCache<SmtTranslationAnnotation>()

internal inline fun <reified T : Any> smtTranslationAnnotation(): SmtTranslationAnnotation =
    smtTranslationAnnotation(T::class)

internal fun <T : Any> smtTranslationAnnotation(kClass: KClass<T>): SmtTranslationAnnotation =
    SMT_TRANSLATION_CACHE.getOrSet(kClass) {
      val legalProperties = mutableListOf<String>()
      (KotlinClassMetadata.readStrict(kClass.java.getAnnotation(Metadata::class.java))
              as KotlinClassMetadata.Class)
          .kmClass
          .properties
          .forEach {
            if (!it.getter.isNotDefault) {
              legalProperties.add(it.name)
            }
          }
      SmtTranslationAnnotation(kClass.qualifiedName, legalProperties.toTypedArray())
    }

internal class SmtTranslationAnnotation(
    private val qualifiedCallerName: String?,
    private val legalProperties: Array<String> = arrayOf()
) {

  fun isLegalProperty(name: String): Boolean = legalProperties.contains(name)

  fun requireLegalProperty(propName: String) {
    require(isLegalProperty(propName)) {
      "The property \"${qualifiedCallerName ?: "?"}.${propName}\" can not be translated. This can happen, for example, due to non-trivial getters."
    }
  }
}
