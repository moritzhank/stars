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

class FunctionBuilder<Return>(
    val allowedTFCCBs: List<TFunCallContextBase<*>>,
    val funs: MutableList<TranslatableFunction<*>> = mutableListOf()
) {

  companion object {

    // function with no parameters (should be not used! or should it?!)
    /*fun <Return> function(init: FunctionBuilder<Return>.() -> Unit): TranslatableFunction<Return> {
      val builder = FunctionBuilder<Return>(listOf())
      init.invoke(builder)
      return builder.funs[0] as TranslatableFunction<Return>
    }
     */

    // function with one parameter
    fun <Param, Return> function(
        init: FunctionBuilder<Return>.(TFunCallContextBase<Param>) -> Unit
    ): TranslatableFunction<Return> {
      val params = listOf(TFunCallContextBase<Param>())
      val builder = FunctionBuilder<Return>(params)
      params[0].ref = builder
      init.invoke(builder, params[0])
      return builder.funs[0] as TranslatableFunction<Return>
    }
  }

  private fun <P, R> buildCallContextWrapper(tfccb: TFunCallContext<P, R>): CallContextWrapper<R> =
      assert(isAllowedTFCCB(tfccb)).let { CallContextWrapper(tfccb) }

  private fun isAllowedTFCCB(tfccb: TFunCallContext<*, *>) = allowedTFCCBs.contains(tfccb.base)

  private fun <T : Number> buildAdd(): Add<T> =
      assert(funs.size == 2).let {
        Add(funs[0] as TranslatableFunction<T>, funs[1] as TranslatableFunction<T>)
      }

  fun FunctionBuilder<Return>.wrap(tfcctx: TFunCallContext<*, Return>): TranslatableFunction<Return> =
      buildCallContextWrapper(tfcctx).also { funs.add(it) }

  fun <T : Number> FunctionBuilder<T>.add(init: FunctionBuilder<T>.() -> Unit): Add<T> {
    return FunctionBuilder<T>(allowedTFCCBs).apply(init).buildAdd<T>().also { funs.add(it) }
  }
}
