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

import java.lang.ref.SoftReference
import kotlin.reflect.KClass

/*
 * The code below is a modified version of the caching implementation
 * of kotlinx.serialization, which is licensed under Apache 2.0.
 * The unmodified version can be found at:
 * https://github.com/Kotlin/kotlinx.serialization/blob/d4d066d72a9f92f06c640be5a36a22f75d0d7659/core/jvmMain/src/kotlinx/serialization/internal/Caching.kt
 */

/** Maps classes to values without classloader leak */
class ClassValueCache<T> {

  private val classValue = ClassValueReferences<CacheEntry<T>>()

  fun getOrSet(key: KClass<*>, factory: () -> T): T =
      classValue.getOrSet(key.java) { CacheEntry(factory()) }.content
}

private class ClassValueReferences<T> : ClassValue<MutableSoftReference<T>>() {

  override fun computeValue(type: Class<*>): MutableSoftReference<T> {
    return MutableSoftReference()
  }

  inline fun getOrSet(key: Class<*>, crossinline factory: () -> T): T {
    val ref: MutableSoftReference<T> = get(key)
    ref.reference.get()?.let {
      return it
    }
    return ref.getOrSetWithLock { factory() }
  }
}

private class CacheEntry<T>(@JvmField val content: T)

private class MutableSoftReference<T> {

  @JvmField @Volatile var reference: SoftReference<T> = SoftReference(null)

  @Synchronized
  fun getOrSetWithLock(factory: () -> T): T {
    reference.get()?.let {
      return it
    }
    val value = factory()
    reference = SoftReference(value)
    return value
  }
}
