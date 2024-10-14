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

@file:Suppress("UNCHECKED_CAST", "unused")

package tools.aqua.stars.logic.kcmftbl.dsl

import kotlin.reflect.KCallable

class FunctionBuilder<Return>(
    allowedCCBs: List<CallContextBase<*>>,
    registeredFunctions: MutableMap<KCallable<*>, TranslatableFunction<*>>,
    val funs: MutableList<TranslatableFunction<*>> = mutableListOf()
) : DSLBuilder(allowedCCBs, registeredFunctions) {

  companion object {

    // function with no parameters
    fun <Return> function(init: FunctionBuilder<Return>.() -> Unit): TFunction<Return> {
      val builder = FunctionBuilder<Return>(listOf(), mutableMapOf())
      init.invoke(builder)
      return TFuncImpl(builder.funs[0] as TranslatableFunction<Return>)
    }

    // function with one parameter
    fun <Param, Return> function(
        init: FunctionBuilder<Return>.(CallContextBase<Param>) -> Unit
    ): T2Function<Param, Return> {
      val params = listOf(CallContextBase<Param>())
      val builder = FunctionBuilder<Return>(params, mutableMapOf())
      params[0].dslBuilder = builder
      init.invoke(builder, params[0])
      return T2FuncImpl(builder.funs[0] as TranslatableFunction<Return>)
    }

    // function with two parameters
    fun <Param1, Param2, Return> function(
        init: FunctionBuilder<Return>.(CallContextBase<Param1>, CallContextBase<Param2>) -> Unit
    ): T3Function<Param1, Param2, Return> {
      val param1 = CallContextBase<Param1>()
      val param2 = CallContextBase<Param2>()
      val builder = FunctionBuilder<Return>(listOf(param1, param2), mutableMapOf())
      param1.dslBuilder = builder
      param2.dslBuilder = builder
      init.invoke(builder, param1, param2)
      return T3FuncImpl(builder.funs[0] as TranslatableFunction<Return>)
    }

    // function with three parameters
    fun <Param1, Param2, Param3, Return> function(
        init:
            FunctionBuilder<Return>.(
                CallContextBase<Param1>, CallContextBase<Param2>, CallContextBase<Param3>) -> Unit
    ): T4Function<Param1, Param2, Param3, Return> {
      val param1 = CallContextBase<Param1>()
      val param2 = CallContextBase<Param2>()
      val param3 = CallContextBase<Param3>()
      val builder = FunctionBuilder<Return>(listOf(param1, param2, param3), mutableMapOf())
      param1.dslBuilder = builder
      param2.dslBuilder = builder
      param3.dslBuilder = builder
      init.invoke(builder, param1, param2, param3)
      return T4FuncImpl(builder.funs[0] as TranslatableFunction<Return>)
    }
  }

  private fun <P, R> buildCallContextWrapper(cc: CallContext<P, R>): TFCallContextWrapper<R> =
      assertCCAllowed(cc).let { TFCallContextWrapper(cc) }

  private fun <T> buildEq(): TFEqual<T> =
      assert(funs.size == 2).let {
        TFEqual(funs[0] as TranslatableFunction<T>, funs[1] as TranslatableFunction<T>)
      }

  private fun <T : Number> buildAdd(): TFAdd<T> =
      assert(funs.size == 2).let {
        TFAdd(funs[0] as TranslatableFunction<T>, funs[1] as TranslatableFunction<T>)
      }

  private fun <C, T : Collection<C>> buildFilter(cc: CallContext<*, T>): TFFilter<C, T> =
      assert(funs.size == 1)
          .also { assertCCAllowed(cc) }
          .let { TFFilter(cc, funs[0] as TranslatableFunction<Boolean>) }

  private fun <T> buildITE(funCond: TranslatableFunction<Boolean>): TFITE<T> =
      assert(funs.size == 2).let {
        TFITE(funCond, funs[0] as TranslatableFunction<T>, funs[1] as TranslatableFunction<T>)
      }

  fun FunctionBuilder<Return>.wrap(cc: CallContext<*, Return>): TranslatableFunction<Return> =
      buildCallContextWrapper(cc).also { funs.add(it) }

  fun <T : Number> const(content: T) = TFConstant(content).also { funs.add(it) }

  fun const(content: Boolean) = TFBConstant(content).also { funs.add(it) }

  fun <T> FunctionBuilder<Boolean>.eq(init: FunctionBuilder<T>.() -> Unit): TFEqual<T> {
    return FunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap())
        .apply(init)
        .buildEq<T>()
        .also { funs.add(it) }
  }

  // Syntax-shortcut for eq
  infix fun <T> CallContext<*, T>.eq(other: CallContext<*, T>): TranslatableFunction<Boolean> {
    val fb = FunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap())
    fb.funs.add(buildCallContextWrapper(this))
    fb.funs.add(buildCallContextWrapper(other))
    return fb.buildEq<T>().also { funs.add(it) }
  }

  fun <T : Number> FunctionBuilder<T>.add(init: FunctionBuilder<T>.() -> Unit): TFAdd<T> {
    return FunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap())
        .apply(init)
        .buildAdd<T>()
        .also { funs.add(it) }
  }

  fun <C, T : Collection<C>> FunctionBuilder<T>.filter(
      collection: CallContext<*, T>,
      init: FunctionBuilder<Boolean>.(CallContextBase<C>) -> Unit
  ): TFFilter<C, T> {
    val ccb = CallContextBase<C>()
    val fb = FunctionBuilder<Boolean>(allowedCCBs.plus(ccb), registeredFunctions.toMutableMap())
    ccb.dslBuilder = fb
    init.invoke(fb, ccb)
    return fb.buildFilter(collection).also { funs.add(it) }
  }

  fun <T> FunctionBuilder<T>.cond(init: FunctionBuilder<Boolean>.() -> Unit): TFITECond<T> {
    val funBuilder =
        FunctionBuilder<Boolean>(allowedCCBs, registeredFunctions.toMutableMap()).apply(init)
    assert(funBuilder.funs.size == 1)
    return TFITECond(
        funBuilder.funs[0] as TranslatableFunction<Boolean>,
        funBuilder.allowedCCBs,
        registeredFunctions.toMutableMap())
  }
}

private class TFuncImpl<Return>(override val tfunc: TranslatableFunction<Return>) :
    TFunction<Return>

private class T2FuncImpl<Param, Return>(override val tfunc: TranslatableFunction<Return>) :
    T2Function<Param, Return>

private class T3FuncImpl<Param1, Param2, Return>(override val tfunc: TranslatableFunction<Return>) :
    T3Function<Param1, Param2, Return>

private class T4FuncImpl<Param1, Param2, Param3, Return>(
    override val tfunc: TranslatableFunction<Return>
) : T4Function<Param1, Param2, Param3, Return>

class TFITECond<T>(
    val cond: TranslatableFunction<Boolean>,
    val allowedCCBs: List<CallContextBase<*>>,
    val registeredFunctions: MutableMap<KCallable<*>, TranslatableFunction<*>>
) {

  fun satisfied(init: FunctionBuilder<T>.() -> Unit): TFITEThen<T> {
    val funBuilder = FunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap()).apply(init)
    assert(funBuilder.funs.size == 1)
    return TFITEThen(
        cond,
        funBuilder.funs[0] as TranslatableFunction<T>,
        funBuilder.allowedCCBs,
        registeredFunctions.toMutableMap())
  }
}

class TFITEThen<T>(
    val cond: TranslatableFunction<Boolean>,
    val then: TranslatableFunction<T>,
    val allowedCCBs: List<CallContextBase<*>>,
    val registeredFunctions: MutableMap<KCallable<*>, TranslatableFunction<*>>
) {

  fun otherwise(init: FunctionBuilder<T>.() -> Unit): TFITE<T> {
    val funBuilder = FunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap()).apply(init)
    assert(funBuilder.funs.size == 1)
    return TFITE(cond, then, funBuilder.funs[0] as TranslatableFunction<T>)
  }
}
