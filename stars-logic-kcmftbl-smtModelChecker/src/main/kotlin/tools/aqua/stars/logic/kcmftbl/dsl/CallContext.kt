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

typealias CCB<Base> = CallContextBase<Base>

class CallContextBase<Base> {

  operator fun <Return> times(prop: KProperty1<Base, Return>): CallContext<Base, Base, Return> =
      PropertyCallContext(prop, null)
  operator fun <Return> times(prop: KFunction1<Base, Return>): CallContext<Base, Base, Return> =
      Function1CallContext(prop, null)
  operator fun <Return, Param> times(
      prop: KFunction2<Base, Param, Return>
  ): Callable2CallContext<Base, Base, Param, Return> = Function2CallContext(prop, null)
  operator fun <Return, Param1, Param2> times(
      prop: KFunction3<Base, Param1, Param2, Return>
  ): Callable3CallContext<Base, Base, Param1, Param2, Return> = Function3CallContext(prop, null)
}

sealed interface CallContext<Base, Caller, Return> {

  val before: CallContext<Base, *, Caller>?
  operator fun <W> times(prop: KProperty1<Return, W>): CallContext<Base, Return, W> =
      PropertyCallContext(prop, this)
  operator fun <W> times(prop: KFunction1<Return, W>): CallContext<Base, Return, W> =
      Function1CallContext(prop, this)
  operator fun <W, P> times(
      prop: KFunction2<Return, P, W>
  ): Callable2CallContext<Base, Return, P, W> = Function2CallContext(prop, this)
  operator fun <W, P1, P2> times(
      prop: KFunction3<Return, P1, P2, W>
  ): Callable3CallContext<Base, Return, P1, P2, W> = Function3CallContext(prop, this)
  infix fun and(callContext: CallContext<Base, *, *>) = Pair(this, callContext)
}

sealed interface Callable2CallContext<Base, Caller, Param, Return> :
    CallContext<Base, Caller, Return> {

  var param: CallContext<Base, *, Param>?
  infix fun withParam(
      configParam: (b: CallContextBase<Base>) -> CallContext<Base, *, Param>
  ): Callable2CallContext<Base, Caller, Param, Return> =
      this.apply { param = configParam(CallContextBase()) }
}

sealed interface Callable3CallContext<Base, Caller, Param1, Param2, Return> :
    CallContext<Base, Caller, Return> {

  var param1: CallContext<Base, *, Param1>?
  var param2: CallContext<Base, *, Param2>?
  infix fun withParams(
      configParam:
          (b: CallContextBase<Base>) -> Pair<
                  CallContext<Base, *, Param1>, CallContext<Base, *, Param2>>
  ): Callable3CallContext<Base, Caller, Param1, Param2, Return> =
      this.apply {
        val (p1, p2) = configParam(CallContextBase())
        param1 = p1
        param2 = p2
      }
}

private class PropertyCallContext<Base, Caller, Return>(
    val prop: KProperty1<Caller, Return>,
    override val before: CallContext<Base, *, Caller>? = null
) : CallContext<Base, Caller, Return>

private class Function1CallContext<Base, Caller, Return>(
    val func: KFunction1<Caller, Return>,
    override val before: CallContext<Base, *, Caller>? = null
) : CallContext<Base, Caller, Return>

private class Function2CallContext<Base, Caller, Param, Return>(
    val func: KFunction2<Caller, Param, Return>,
    override val before: CallContext<Base, *, Caller>? = null
) : Callable2CallContext<Base, Caller, Param, Return> {

  override var param: CallContext<Base, *, Param>? = null
}

private class Function3CallContext<Base, Caller, Param1, Param2, Return>(
    val func: KFunction3<Caller, Param1, Param2, Return>,
    override val before: CallContext<Base, *, Caller>? = null
) : Callable3CallContext<Base, Caller, Param1, Param2, Return> {

  override var param1: CallContext<Base, *, Param1>? = null
  override var param2: CallContext<Base, *, Param2>? = null
}
