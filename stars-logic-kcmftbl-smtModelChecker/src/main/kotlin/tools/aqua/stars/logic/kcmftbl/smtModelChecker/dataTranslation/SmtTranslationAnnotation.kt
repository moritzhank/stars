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

import java.lang.reflect.ParameterizedType
import kotlin.reflect.KClass
import kotlin.reflect.javaType
import kotlinx.metadata.isNotDefault
import kotlinx.metadata.jvm.KotlinClassMetadata
import kotlinx.serialization.Transient
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.ClassValueCache

/** Contains a list of legal (translation-related) properties of a class. */
internal class SmtTranslationAnnotation(
    private val qualifiedCallerName: String?,
    private val legalProperties: Array<Property> = arrayOf()
) {

  private fun isLegalProperty(name: String): Boolean = legalProperties.any { it.name == name }

  fun requireLegalProperty(propName: String) {
    require(isLegalProperty(propName)) {
      "The property \"${qualifiedCallerName ?: "?"}.${propName}\" can not be translated. This can happen, for example, due to non-trivial getters."
    }
  }

  fun getLegalProperties() = legalProperties

  class Property(val name: String, val clazz: Class<*>?, val firstTypeArgument: Class<*>? = null)
}

internal val SMT_TRANSLATION_CACHE = ClassValueCache<SmtTranslationAnnotation>()

@OptIn(ExperimentalStdlibApi::class)
internal fun <T : Any> smtTranslationAnnotation(kClass: KClass<T>): SmtTranslationAnnotation =
    SMT_TRANSLATION_CACHE.getOrSet(kClass) {
      val legalProperties = mutableListOf<SmtTranslationAnnotation.Property>()
      // Part below is adapted from
      // https://discuss.kotlinlang.org/t/reflection-and-properties-checking-for-custom-getters-setters/22457/2
      (KotlinClassMetadata.readStrict(kClass.java.getAnnotation(Metadata::class.java))
              as KotlinClassMetadata.Class)
          .kmClass
          .properties
          .forEach { kmProperty ->
            if (!kmProperty.getter.isNotDefault) {
              val propertyName = kmProperty.name
              val member = kClass.members.first { it.name == propertyName }
              if (!member.annotations.any { it is Transient }) {
                val memberReturnType = member.returnType.javaType
                var memberClass: Class<*>? = null
                var memberFirstTypeArg: Class<*>? = null
                if (memberReturnType !is ParameterizedType) {
                  memberClass = memberReturnType as Class<*>
                } else if(memberReturnType.rawType.typeName == List::class.java.name) {
                  memberFirstTypeArg = memberReturnType.actualTypeArguments[0] as Class<*>
                }
                // Override enums to be integers
                if (memberClass?.isEnum == true) {
                  memberClass = Int::class.java
                }
                legalProperties.add(SmtTranslationAnnotation.Property(propertyName, memberClass, memberFirstTypeArg))
              }
            }
          }
      SmtTranslationAnnotation(kClass.qualifiedName, legalProperties.toTypedArray())
    }
