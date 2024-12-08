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

@file:Suppress("Unused", "UseDataClass")

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation

import kotlin.reflect.KClass
import kotlin.reflect.full.findAnnotation
import kotlin.reflect.full.hasAnnotation
import kotlin.reflect.full.memberProperties
import kotlin.reflect.javaType
import kotlinx.metadata.isNotDefault
import kotlinx.serialization.SerialName
import kotlinx.serialization.Transient
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.encoding.SmtAllowNonTrivialGetter
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.ClassValueCache
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.getKmProperties
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.getQualifiedName
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.resolveClassAndGenericArgumentClass

/** Stores a list of translatable properties of a class. */
internal class SmtTranslationClassInfo(
    /** Name of the translated class. */
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

internal val SMT_TRANSLATION_CACHE = ClassValueCache<SmtTranslationClassInfo>()

/** Generate SmtTranslationClassInfo for [kClass] or get it from [SMT_TRANSLATION_CACHE]. */
@OptIn(ExperimentalStdlibApi::class)
internal fun <T : Any> smtTranslationClassInfo(kClass: KClass<T>): SmtTranslationClassInfo {
  // Lambda expression to calculate the SmtTranslationClassInfo for kClass
  val smtTranslationClassInfoFactory: () -> SmtTranslationClassInfo = {
    val translationName: String =
        kClass.findAnnotation<SerialName>()?.value ?: getQualifiedName(kClass)
    val translatableProperties = mutableListOf<SmtTranslationClassInfo.Property>()
    for (kmProperty in getKmProperties(kClass)) {
      // Get the kProperty associated with kmProperty
      val kProperty = kClass.memberProperties.find { it.name == kmProperty.name }!!
      // Skip properties with Transient annotation
      if (kProperty.hasAnnotation<Transient>()) {
        continue
      }
      // Skip non-trivial getter if they are not annotated with SmtAllowNonTrivialGetter
      var isNonTrivialGetter = false
      if (kmProperty.getter.isNotDefault) {
        if (!kProperty.hasAnnotation<SmtAllowNonTrivialGetter>()) {
          continue
        }
        isNonTrivialGetter = true
      }
      // Resolve the class of the property and, if possible, the generic type
      val resolvedClassPair =
          try {
            resolveClassAndGenericArgumentClass(kProperty.returnType.javaType)
          } catch (err: IllegalStateException) {
            // Ignoring any type that is no class
            continue
          } catch (err: IllegalArgumentException) {
            // Ignoring any generic type whose generic argument is itself generic or no class
            continue
          }
      var clazz = resolvedClassPair.first
      val genericArgumentClass = resolvedClassPair.second
      // Lambda expression to check if class is translatable
      val isTranslatable: (Class<*>) -> Boolean = { !it.isSealed && !it.isInterface }
      // Ignore non-generic classes that cannot be translated
      if (genericArgumentClass == null && !isTranslatable(clazz)) {
        continue
      }
      if (genericArgumentClass != null) {
        // Ignore all generic types that are not lists
        if (clazz.typeName != List::class.java.name) {
          continue
        }
        // Ignore all generic types where the generic argument cannot be translated
        if (!isTranslatable(genericArgumentClass)) {
          continue
        }
      }
      // Override enums to be integers
      if (clazz.isEnum) {
        clazz = Int::class.java
      }
      val newProperty =
          SmtTranslationClassInfo.Property(
              kProperty.name, isNonTrivialGetter, clazz, genericArgumentClass)
      translatableProperties.add(newProperty)
    }
    SmtTranslationClassInfo(translationName, translatableProperties.toTypedArray())
  }
  return SMT_TRANSLATION_CACHE.getOrSet(kClass, smtTranslationClassInfoFactory)
}
