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

import kotlinx.metadata.isNotDefault
import kotlinx.metadata.jvm.KotlinClassMetadata

internal val SMT_TRANSLATION_CACHE = ClassValueCache<SmtTranslationAnnotation>()

internal inline fun <reified T> smtTranslationAnnotation(): SmtTranslationAnnotation =
    SMT_TRANSLATION_CACHE.getOrSet(T::class) {
      val legalProperties = mutableListOf<String>()
      (KotlinClassMetadata.readStrict(T::class.java.getAnnotation(Metadata::class.java))
              as KotlinClassMetadata.Class)
          .kmClass
          .properties
          .forEach {
            if (!it.getter.isNotDefault) {
              legalProperties.add(it.name)
            }
          }
      SmtTranslationAnnotation(legalProperties.toTypedArray())
    }

class SmtTranslationAnnotation(val legalArguments: Array<String> = arrayOf())
