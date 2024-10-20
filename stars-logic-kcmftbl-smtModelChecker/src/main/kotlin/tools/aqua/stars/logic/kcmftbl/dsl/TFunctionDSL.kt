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

class TFunctionBuilder<Return>(
    allowedCCBs: List<CallContextBase<*>>,
    registeredFunctions: MutableMap<KCallable<*>, TNFunction<*>>,
    private val funs: MutableList<TFunction<*>> = mutableListOf()
) : DSLBuilder(allowedCCBs, registeredFunctions) {

  companion object {

    /** Define function with no parameters */
    fun <Return> function(init: TFunctionBuilder<Return>.() -> Unit): T1Function<Return> {
      val builder = TFunctionBuilder<Return>(listOf(), mutableMapOf())
      init.invoke(builder)
      return T1FunctionImpl(builder.funs[0] as TFunction<Return>)
    }

    /** Define function with one parameter */
    fun <Param, Return> function(
        init: TFunctionBuilder<Return>.(CallContextBase<Param>) -> Unit
    ): T2Function<Param, Return> {
      val params = listOf(CallContextBase<Param>())
      val builder = TFunctionBuilder<Return>(params, mutableMapOf())
      params[0].dslBuilder = builder
      init.invoke(builder, params[0])
      return T2FunctionImpl(builder.funs[0] as TFunction<Return>)
    }

    /** Define function with two parameters */
    fun <Param1, Param2, Return> function(
        init: TFunctionBuilder<Return>.(CallContextBase<Param1>, CallContextBase<Param2>) -> Unit
    ): T3Function<Param1, Param2, Return> {
      val param1 = CallContextBase<Param1>()
      val param2 = CallContextBase<Param2>()
      val builder = TFunctionBuilder<Return>(listOf(param1, param2), mutableMapOf())
      param1.dslBuilder = builder
      param2.dslBuilder = builder
      init.invoke(builder, param1, param2)
      return T3FunctionImpl(builder.funs[0] as TFunction<Return>)
    }

    /** Define function with three parameters */
    fun <Param1, Param2, Param3, Return> function(
        init:
            TFunctionBuilder<Return>.(
                CallContextBase<Param1>, CallContextBase<Param2>, CallContextBase<Param3>) -> Unit
    ): T4Function<Param1, Param2, Param3, Return> {
      val param1 = CallContextBase<Param1>()
      val param2 = CallContextBase<Param2>()
      val param3 = CallContextBase<Param3>()
      val builder = TFunctionBuilder<Return>(listOf(param1, param2, param3), mutableMapOf())
      param1.dslBuilder = builder
      param2.dslBuilder = builder
      param3.dslBuilder = builder
      init.invoke(builder, param1, param2, param3)
      return T4FunctionImpl(builder.funs[0] as TFunction<Return>)
    }
  }

  private fun <P, R> buildCallContextWrapper(cc: CallContext<P, R>): TFCallContextWrapper<R> =
      assertCallContextAllowed(cc).let { TFCallContextWrapper(cc) }

  private fun <T> buildComparison(relation: Relation): TFComparison<T> =
      assert(funs.size == 2).let {
        TFComparison(funs[0] as TFunction<T>, funs[1] as TFunction<T>, relation)
      }

  private fun <T : Number> buildAdd(): TFAdd<T> =
      assert(funs.size == 2).let { TFAdd(funs[0] as TFunction<T>, funs[1] as TFunction<T>) }

  private fun <C, T : Collection<C>> buildFilter(cc: CallContext<*, T>): TFFilter<C, T> =
      assert(funs.size == 1)
          .also { assertCallContextAllowed(cc) }
          .let { TFFilter(cc, funs[0] as TFunction<Boolean>) }

  private fun <T> buildBranch(funCond: TFunction<Boolean>): TFBranch<T> =
      assert(funs.size == 2).let {
        TFBranch(funCond, funs[0] as TFunction<T>, funs[1] as TFunction<T>)
      }

  fun TFunctionBuilder<Return>.wrap(cc: CallContext<*, Return>): TFunction<Return> =
      buildCallContextWrapper(cc).also { funs.add(it) }

  fun <T : Number> const(content: T) = TFConstantNumber(content).also { funs.add(it) }

  fun const(content: Boolean) = TFConstantBoolean(content).also { funs.add(it) }

  private fun <T> comparison(
      cc1: CallContext<*, T>,
      cc2: CallContext<*, T>,
      relation: Relation
  ): TFComparison<T> {
    val funcBuilder = TFunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap())
    funcBuilder.funs.add(buildCallContextWrapper(cc1))
    funcBuilder.funs.add(buildCallContextWrapper(cc2))
    return funcBuilder.buildComparison<T>(relation).also { funs.add(it) }
  }

  fun <T> TFunctionBuilder<Boolean>.eq(init: TFunctionBuilder<T>.() -> Unit): TFComparison<T> {
    return TFunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap())
        .apply(init)
        .buildComparison<T>(Relation.Eq)
        .also { funs.add(it) }
  }

  infix fun <T> CallContext<*, T>.leq(other: CallContext<*, T>): TFunction<Boolean> =
      comparison(this, other, Relation.Leq)

  infix fun <T> CallContext<*, T>.geq(other: CallContext<*, T>): TFunction<Boolean> =
      comparison(this, other, Relation.Geq)

  infix fun <T> CallContext<*, T>.lt(other: CallContext<*, T>): TFunction<Boolean> =
      comparison(this, other, Relation.Lt)

  infix fun <T> CallContext<*, T>.gt(other: CallContext<*, T>): TFunction<Boolean> =
      comparison(this, other, Relation.Gt)

  infix fun <T> CallContext<*, T>.eq(other: CallContext<*, T>): TFunction<Boolean> =
      comparison(this, other, Relation.Eq)

  infix fun <T> CallContext<*, T>.ne(other: CallContext<*, T>): TFunction<Boolean> =
      comparison(this, other, Relation.Ne)

  fun <T : Number> TFunctionBuilder<T>.add(init: TFunctionBuilder<T>.() -> Unit): TFAdd<T> {
    return TFunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap())
        .apply(init)
        .buildAdd<T>()
        .also { funs.add(it) }
  }

  fun <C, T : Collection<C>> TFunctionBuilder<T>.filter(
      collection: CallContext<*, T>,
      init: TFunctionBuilder<Boolean>.(CallContextBase<C>) -> Unit
  ): TFFilter<C, T> {
    val ccb = CallContextBase<C>()
    val fb = TFunctionBuilder<Boolean>(allowedCCBs.plus(ccb), registeredFunctions.toMutableMap())
    ccb.dslBuilder = fb
    init.invoke(fb, ccb)
    return fb.buildFilter(collection).also { funs.add(it) }
  }

  fun <T> TFunctionBuilder<T>.branch(
      init: TFunctionBuilder<Boolean>.() -> Unit
  ): TFBranchCondition<T> {
    val funBuilder =
        TFunctionBuilder<Boolean>(allowedCCBs, registeredFunctions.toMutableMap()).apply(init)
    assert(funBuilder.funs.size == 1)
    return TFBranchCondition(
        funBuilder.funs[0] as TFunction<Boolean>, this, this.allowedCCBs, this.registeredFunctions)
  }

  class TFBranchCondition<T>(
      private val condition: TFunction<Boolean>,
      private val initialBuilder: TFunctionBuilder<T>,
      private val allowedCCBs: List<CallContextBase<*>>,
      private val registeredFunctions: MutableMap<KCallable<*>, TNFunction<*>>
  ) {

    fun satisfied(init: TFunctionBuilder<T>.() -> Unit): TFBranchSatisfied<T> {
      val funBuilder =
          TFunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap()).apply(init)
      assert(funBuilder.funs.size == 1)
      return TFBranchSatisfied(
          condition,
          funBuilder.funs[0] as TFunction<T>,
          initialBuilder,
          allowedCCBs,
          registeredFunctions.toMutableMap())
    }
  }

  class TFBranchSatisfied<T>(
      private val condition: TFunction<Boolean>,
      private val satisfied: TFunction<T>,
      private val initialBuilder: TFunctionBuilder<T>,
      private val allowedCCBs: List<CallContextBase<*>>,
      private val registeredFunctions: MutableMap<KCallable<*>, TNFunction<*>>
  ) {

    fun otherwise(init: TFunctionBuilder<T>.() -> Unit): TFBranch<T> {
      val funBuilder =
          TFunctionBuilder<T>(allowedCCBs, registeredFunctions.toMutableMap()).apply(init)
      assert(funBuilder.funs.size == 1)
      return TFBranch(condition, satisfied, funBuilder.funs[0] as TFunction<T>).also {
        initialBuilder.funs.add(it)
      }
    }
  }
}

private class T1FunctionImpl<Return>(override val func: TFunction<Return>) : T1Function<Return>

private class T2FunctionImpl<Param, Return>(override val func: TFunction<Return>) :
    T2Function<Param, Return>

private class T3FunctionImpl<Param1, Param2, Return>(override val func: TFunction<Return>) :
    T3Function<Param1, Param2, Return>

private class T4FunctionImpl<Param1, Param2, Param3, Return>(override val func: TFunction<Return>) :
    T4Function<Param1, Param2, Param3, Return>
