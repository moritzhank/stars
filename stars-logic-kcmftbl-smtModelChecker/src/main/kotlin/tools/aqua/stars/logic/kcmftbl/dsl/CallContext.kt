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
  val base: CallContextBase<*>

  operator fun <W> times(prop: KProperty1<Return, W>): CallContext<Return, W> =
      PropertyCallContext(prop, this, base)

  operator fun <W> times(func: KFunction1<Return, W>): CallContext<Return, W> =
      Function1CallContext(func, this, base)

  operator fun <W, P> times(func: KFunction2<Return, P, W>): Callable2CallContext<Return, P, W> =
      Function2CallContext(func, this, base)

  operator fun <W, P1, P2> times(
      func: KFunction3<Return, P1, P2, W>
  ): Callable3CallContext<Return, P1, P2, W> = Function3CallContext(func, this, base)
}

class CallContextBase<Type>() : CallContext<Nothing, Type> {

  override val before: CallContext<*, Nothing>? = null
  override val base: CallContextBase<*> = this
  lateinit var dslBuilder: DSLBuilder
  var debugInfo: String? = null

  override fun toString(): String = debugInfo ?: super.toString()

  override operator fun <Return> times(prop: KProperty1<Type, Return>): CallContext<Type, Return> =
      PropertyCallContext(prop, null, base)

  override operator fun <Return> times(func: KFunction1<Type, Return>): CallContext<Type, Return> =
      Function1CallContext(func, null, base)

  override operator fun <Return, Param> times(
      func: KFunction2<Type, Param, Return>
  ): Callable2CallContext<Type, Param, Return> = Function2CallContext(func, null, base)

  override operator fun <Return, Param1, Param2> times(
      func: KFunction3<Type, Param1, Param2, Return>
  ): Callable3CallContext<Type, Param1, Param2, Return> = Function3CallContext(func, null, base)
}

sealed interface PropAccessibleCallContext<Caller, Return> : CallContext<Caller, Return> {

  val prop: KProperty1<Caller, Return>
}

sealed interface Callable1CallContext<Caller, Return> : CallContext<Caller, Return> {

  val func: KFunction1<Caller, Return>
}

sealed interface Callable2CallContext<Caller, Param, Return> {

  fun withParam(cc: CallContext<*, Param>): PCallable2CallContext<Caller, Param, Return>
}

sealed interface PCallable2CallContext<Caller, Param, Return> : CallContext<Caller, Return> {

  val func: KFunction2<Caller, Param, Return>
  val param: CallContext<*, Param>
}

sealed interface Callable3CallContext<Caller, Param1, Param2, Return> {

  fun withParams(
      cc1: CallContext<*, Param1>,
      cc2: CallContext<*, Param2>
  ): PCallable3CallContext<Caller, Param1, Param2, Return>
}

sealed interface PCallable3CallContext<Caller, Param1, Param2, Return> :
    CallContext<Caller, Return> {

  val func: KFunction3<Caller, Param1, Param2, Return>
  val param1: CallContext<*, Param1>
  val param2: CallContext<*, Param2>
}

private class PropertyCallContext<Caller, Return>(
    override val prop: KProperty1<Caller, Return>,
    override val before: CallContext<*, Caller>?,
    override val base: CallContextBase<*>
) : PropAccessibleCallContext<Caller, Return>

private class Function1CallContext<Caller, Return>(
    override val func: KFunction1<Caller, Return>,
    override val before: CallContext<*, Caller>?,
    override val base: CallContextBase<*>
) : Callable1CallContext<Caller, Return>

private class Function2CallContext<Caller, Param, Return>(
    private val func: KFunction2<Caller, Param, Return>,
    private val before: CallContext<*, Caller>?,
    private val base: CallContextBase<*>
) : Callable2CallContext<Caller, Param, Return> {

  override fun withParam(cc: CallContext<*, Param>): PCallable2CallContext<Caller, Param, Return> =
      base.dslBuilder.assertCCAllowed(cc).let { PFunction2CallContext(func, before, base, cc) }
}

private class PFunction2CallContext<Caller, Param, Return>(
    override val func: KFunction2<Caller, Param, Return>,
    override val before: CallContext<*, Caller>?,
    override val base: CallContextBase<*>,
    override val param: CallContext<*, Param>
) : PCallable2CallContext<Caller, Param, Return>

private class Function3CallContext<Caller, Param1, Param2, Return>(
    private val func: KFunction3<Caller, Param1, Param2, Return>,
    private val before: CallContext<*, Caller>?,
    private val base: CallContextBase<*>
) : Callable3CallContext<Caller, Param1, Param2, Return> {

  override fun withParams(
      cc1: CallContext<*, Param1>,
      cc2: CallContext<*, Param2>
  ): PCallable3CallContext<Caller, Param1, Param2, Return> =
      base.dslBuilder
          .assertCCAllowed(cc1)
          .also { base.dslBuilder.assertCCAllowed(cc2) }
          .let { PFunction3CallContext(func, before, base, cc1, cc2) }
}

private class PFunction3CallContext<Caller, Param1, Param2, Return>(
    override val func: KFunction3<Caller, Param1, Param2, Return>,
    override val before: CallContext<*, Caller>?,
    override val base: CallContextBase<*>,
    override val param1: CallContext<*, Param1>,
    override val param2: CallContext<*, Param2>
) : PCallable3CallContext<Caller, Param1, Param2, Return>
