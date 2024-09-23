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

@file:Suppress("unused")

package tools.aqua.stars.logic.kcmftbl.dsl

import kotlin.reflect.KCallable
import kotlin.reflect.KFunction1
import kotlin.reflect.KFunction2
import kotlin.reflect.KFunction3

open class DSLBuilder(
    val allowedCCBs: List<CCB<*>>,
    protected val registeredFunctions: MutableMap<KCallable<*>, TranslatableFunction<*>>
) {

  // Check if CallContext is legal for current DSLBuilder-context
  fun isAllowedCC(cc: CallContext<*, *>): Boolean {
    // Is cc's CallContextBase allowed?
    if (!allowedCCBs.contains(cc.base)) {
      return false
    }
    // Are all function calls registered?
    var elemBefore: CallContext<*, *>? = cc
    while (elemBefore != null) {
      val currentElem = elemBefore.also { elemBefore = elemBefore!!.before }
      val isRegistered =
          when (currentElem) {
            is Callable1CallContext -> registeredFunctions[currentElem.func] != null
            is PCallable2CallContext<*, *, *> -> registeredFunctions[currentElem.func] != null
            is PCallable3CallContext<*, *, *, *> -> registeredFunctions[currentElem.func] != null
            else -> true
          }
      if (!isRegistered) {
        return false
      }
    }
    return true
  }

  fun <Caller, Return> registerFunction(
      callable: KFunction1<Caller, Return>,
      func: T2Function<Caller, Return>
  ) {
    registeredFunctions[callable] = func.tfunc
  }

  fun <Caller, Param, Return> registerFunction(
      callable: KFunction2<Caller, Param, Return>,
      func: T3Function<Caller, Param, Return>
  ) {
    registeredFunctions[callable] = func.tfunc
  }

  fun <Caller, Param1, Param2, Return> registerFunction(
      callable: KFunction3<Caller, Param1, Param2, Return>,
      func: T4Function<Caller, Param1, Param2, Return>
  ) {
    registeredFunctions[callable] = func.tfunc
  }
}
