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

package tools.aqua.stars.logic.kcmftbl.dsl

import kotlin.reflect.KFunction1
import kotlin.reflect.KFunction2
import kotlin.reflect.KFunction3
import kotlin.reflect.KProperty1

class CallContextBase<B> {

  operator fun <R> times(prop: KProperty1<B, R>): CallContext<B, B, R> =
      PropertyCallContext(prop, null)
  operator fun <R> times(prop: KFunction1<B, R>): CallContext<B, B, R> =
      Function1CallContext(prop, null)
  operator fun <R, P> times(prop: KFunction2<B, P, R>): Callable2CallContext<B, B, P, R> =
      Function2CallContext(prop, null)
  operator fun <R, P1, P2> times(
      prop: KFunction3<B, P1, P2, R>
  ): Callable3CallContext<B, B, P1, P2, R> = Function3CallContext(prop, null)
}

sealed interface CallContext<B, C, R> {

  val before: CallContext<B, *, C>?
  operator fun <W> times(prop: KProperty1<R, W>): CallContext<B, R, W> =
      PropertyCallContext(prop, this)
  operator fun <W> times(prop: KFunction1<R, W>): CallContext<B, R, W> =
      Function1CallContext(prop, this)
  operator fun <W, P> times(prop: KFunction2<R, P, W>): Callable2CallContext<B, R, P, W> =
      Function2CallContext(prop, this)
  operator fun <W, P1, P2> times(
      prop: KFunction3<R, P1, P2, W>
  ): Callable3CallContext<B, R, P1, P2, W> = Function3CallContext(prop, this)
  infix fun and(callContext: CallContext<B, *, *>) = Pair(this, callContext)
}

sealed interface Callable2CallContext<B, C, P, R> : CallContext<B, C, R> {

  var param: CallContext<B, *, P>?
  infix fun withParam(
      configParam: (b: CallContextBase<B>) -> CallContext<B, *, P>
  ): Callable2CallContext<B, C, P, R> = this.apply { param = configParam(CallContextBase()) }
}

sealed interface Callable3CallContext<B, C, P1, P2, R> : CallContext<B, C, R> {

  var param1: CallContext<B, *, P1>?
  var param2: CallContext<B, *, P2>?
  infix fun withParams(
      configParam: (b: CallContextBase<B>) -> Pair<CallContext<B, *, P1>, CallContext<B, *, P2>>
  ): Callable3CallContext<B, C, P1, P2, R> =
      this.apply {
        val (p1, p2) = configParam(CallContextBase())
        param1 = p1
        param2 = p2
      }
}

private class PropertyCallContext<B, C, R>(
    val prop: KProperty1<C, R>,
    override val before: CallContext<B, *, C>? = null
) : CallContext<B, C, R>

private class Function1CallContext<B, C, R>(
    val func: KFunction1<C, R>,
    override val before: CallContext<B, *, C>? = null
) : CallContext<B, C, R>

private class Function2CallContext<B, C, P, R>(
    val func: KFunction2<C, P, R>,
    override val before: CallContext<B, *, C>? = null
) : Callable2CallContext<B, C, P, R> {

  override var param: CallContext<B, *, P>? = null
}

private class Function3CallContext<B, C, P1, P2, R>(
    val func: KFunction3<C, P1, P2, R>,
    override val before: CallContext<B, *, C>? = null
) : Callable3CallContext<B, C, P1, P2, R> {

  override var param1: CallContext<B, *, P1>? = null
  override var param2: CallContext<B, *, P2>? = null
}
