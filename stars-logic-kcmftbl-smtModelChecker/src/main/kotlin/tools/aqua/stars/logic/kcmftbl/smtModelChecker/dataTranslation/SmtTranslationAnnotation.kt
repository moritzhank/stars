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
import kotlin.reflect.full.findAnnotation
import kotlin.reflect.full.hasAnnotation
import kotlin.reflect.full.memberProperties
import kotlin.reflect.javaType
import kotlinx.metadata.isNotDefault
import kotlinx.metadata.jvm.KotlinClassMetadata
import kotlinx.serialization.SerialName
import kotlinx.serialization.Transient
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.encoding.SmtAllowNonTrivialGetter
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.ClassValueCache

/** Contains a list of translatable properties of a class. */
internal class SmtTranslationAnnotation(
    private val translationName: String,
    private val properties: Array<Property>
) {

  fun isTranslatableProperty(name: String): Boolean = properties.any { it.name == name }

  fun requireTranslatableProperty(propName: String) {
    require(isTranslatableProperty(propName)) {
      "The property \"$translationName.$propName\" can not be translated. This can happen, for example, due to non-trivial getters."
    }
  }

  fun getTranslatableProperties() = properties

  class Property(
      val name: String,
      val nonTrivialGetter: Boolean,
      val clazz: Class<*>,
      val listTypeArgumentClass: Class<*>? = null
  )
}

internal val SMT_TRANSLATION_CACHE = ClassValueCache<SmtTranslationAnnotation>()

internal fun getQualifiedName(kClass: KClass<*>): String {
  val name = kClass.qualifiedName
  requireNotNull(name) { "No qualified name could be found for \"$kClass\"." }
  return name
}

@OptIn(ExperimentalStdlibApi::class)
internal fun <T : Any> smtTranslationAnnotation(kClass: KClass<T>): SmtTranslationAnnotation =
    SMT_TRANSLATION_CACHE.getOrSet(kClass) {
      val translationName: String =
          kClass.findAnnotation<SerialName>()?.value ?: getQualifiedName(kClass)
      val tranlatableProperties = mutableListOf<SmtTranslationAnnotation.Property>()
      // The Part below is adapted from
      // https://discuss.kotlinlang.org/t/reflection-and-properties-checking-for-custom-getters-setters/22457/2
      val kmProperties =
          (KotlinClassMetadata.readStrict(kClass.java.getAnnotation(Metadata::class.java))
                  as KotlinClassMetadata.Class)
              .kmClass
              .properties
      for (kmProperty in kmProperties) {
        val kProperty = kClass.memberProperties.find { it.name == kmProperty.name }!!
        if (kProperty.hasAnnotation<Transient>()) {
          continue
        }
        var nonTrivialGetter = false
        if (kmProperty.getter.isNotDefault) {
          if (!kProperty.hasAnnotation<SmtAllowNonTrivialGetter>()) {
            continue
          }
          nonTrivialGetter = true
        }
        val returnType = kProperty.returnType.javaType
        var listTypeArgumentClass: Class<*>? = null
        var clazz: Class<*> =
            when (returnType) {
              is Class<*> -> {
                if (!returnType.isTranslatable()) {
                  continue
                }
                returnType
              }
              is ParameterizedType -> {
                if (returnType.rawType.typeName != List::class.java.name) {
                  continue
                }
                val listType = returnType.actualTypeArguments.firstOrNull()
                // Lists with complex type arguments are not yet supported.
                if (listType == null || listType !is Class<*>) {
                  continue
                }
                if (!listType.isTranslatable()) {
                  continue
                }
                listTypeArgumentClass = listType
                returnType.rawType as Class<*>
              }
              else ->
                  error(
                      "Could not retrieve the class of the property \"$translationName.${kProperty.name}\".")
            }
        // Override enums to be integers
        if (clazz.isEnum) {
          clazz = Int::class.java
        }
        tranlatableProperties.add(
            SmtTranslationAnnotation.Property(
                kProperty.name, nonTrivialGetter, clazz, listTypeArgumentClass))
      }
      SmtTranslationAnnotation(translationName, tranlatableProperties.toTypedArray())
    }

private fun Class<*>.isTranslatable(): Boolean {
  return !this.isSealed && !this.isInterface
}

fun getTranslatableProperties(kClass: KClass<*>): List<String> {
  val a = smtTranslationAnnotation(kClass)
  val result = mutableListOf<String>()
  a.getTranslatableProperties().fold(result) { list, prop -> list.apply { add(prop.name) } }
  return result
}
