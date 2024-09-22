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

import kotlin.reflect.KProperty1

typealias TFCCB<Type> = TFunCallContextBase<Type>

sealed interface TFunCallContext<Caller, Return> {

  val before: TFunCallContext<*, Caller>?
  val base: TFunCallContextBase<*>

  operator fun <W> times(prop: KProperty1<Return, W>): TFunCallContext<Return, W> =
      PropertyTFunCallContext(prop, this, base)
}

private class PropertyTFunCallContext<Caller, Return>(
    val prop: KProperty1<Caller, Return>,
    override val before: TFunCallContext<*, Caller>?,
    override val base: TFunCallContextBase<*>
) : TFunCallContext<Caller, Return>

class TFunCallContextBase<Type> : TFunCallContext<Nothing, Type> {

  lateinit var ref: FunctionBuilder<*>
  override val before: TFunCallContext<*, Nothing>? = null
  override val base: TFunCallContextBase<*> = this

  override operator fun <Return> times(
      prop: KProperty1<Type, Return>
  ): TFunCallContext<Type, Return> = PropertyTFunCallContext(prop, this, this)
}
