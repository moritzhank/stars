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

import kotlin.reflect.KFunction1
import kotlin.reflect.KFunction2
import kotlin.reflect.KFunction3
import kotlin.reflect.KProperty1

typealias CCB<Type> = CallContextBase<Type>

sealed interface CallContext<Caller, Return> {

  val before: CallContext<*, Caller>?
  operator fun <W> times(prop: KProperty1<Return, W>): CallContext<Return, W> =
      PropertyCallContext(prop, this)
  operator fun <W> times(func: KFunction1<Return, W>): CallContext<Return, W> =
      Function1CallContext(func, this)
  operator fun <W, P> times(func: KFunction2<Return, P, W>): Callable2CallContext<Return, P, W> =
      Function2CallContext(func, this)
  operator fun <W, P1, P2> times(
      func: KFunction3<Return, P1, P2, W>
  ): Callable3CallContext<Return, P1, P2, W> = Function3CallContext(func, this)
}

class CallContextBase<Type> : CallContext<Nothing, Type> {

  lateinit var formulaRef: Formula
  override val before: CallContext<*, Nothing>? = null
  override operator fun <Return> times(prop: KProperty1<Type, Return>): CallContext<Type, Return> =
      PropertyCallContext(prop, null)
  override operator fun <Return> times(func: KFunction1<Type, Return>): CallContext<Type, Return> =
      Function1CallContext(func, null)
  override operator fun <Return, Param> times(
      func: KFunction2<Type, Param, Return>
  ): Callable2CallContext<Type, Param, Return> = Function2CallContext(func, null)
  override operator fun <Return, Param1, Param2> times(
      func: KFunction3<Type, Param1, Param2, Return>
  ): Callable3CallContext<Type, Param1, Param2, Return> = Function3CallContext(func, null)
}

sealed interface Callable2CallContext<Caller, Param, Return> : CallContext<Caller, Return> {

  var param: CallContext<*, Param>?
  fun withParam(cc: CallContext<*, Param>) = this.apply { param = cc }
}

sealed interface Callable3CallContext<Caller, Param1, Param2, Return> :
    CallContext<Caller, Return> {

  var param1: CallContext<*, Param1>?
  var param2: CallContext<*, Param2>?
  fun withParams(cc1: CallContext<*, Param1>, cc2: CallContext<*, Param2>) =
      this.apply {
        param1 = cc1
        param2 = cc2
      }
}

private class PropertyCallContext<Caller, Return>(
    val prop: KProperty1<Caller, Return>,
    override val before: CallContext<*, Caller>? = null
) : CallContext<Caller, Return>

private class Function1CallContext<Caller, Return>(
    val func: KFunction1<Caller, Return>,
    override val before: CallContext<*, Caller>? = null
) : CallContext<Caller, Return>

private class Function2CallContext<Caller, Param, Return>(
    val func: KFunction2<Caller, Param, Return>,
    override val before: CallContext<*, Caller>? = null
) : Callable2CallContext<Caller, Param, Return> {

  override var param: CallContext<*, Param>? = null
}

private class Function3CallContext<Caller, Param1, Param2, Return>(
    val func: KFunction3<Caller, Param1, Param2, Return>,
    override val before: CallContext<*, Caller>? = null
) : Callable3CallContext<Caller, Param1, Param2, Return> {

  override var param1: CallContext<*, Param1>? = null
  override var param2: CallContext<*, Param2>? = null
}
