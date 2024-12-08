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

@file:Suppress(
    "UndocumentedPublicClass", "UndocumentedPublicFunction", "UndocumentedPublicProperty")

package tools.aqua.stars.logic.kcmftbl.dsl

sealed interface TFunction<Return>

data class TFConstantNumber<T : Number>(val content: T) : TFunction<T>

data class TFConstantBoolean(val content: Boolean) : TFunction<Boolean>

data class TFCallContextWrapper<Return>(
    val callContext: CallContext<*, Return>,
) : TFunction<Return>

data class TFAdd<T : Number>(val lhs: TFunction<T>, val rhs: TFunction<T>) : TFunction<T>

data class TFComparison<T>(val lhs: TFunction<T>, val rhs: TFunction<T>, val relation: Relation) :
    TFunction<Boolean>

data class TFFilter<C, T : Collection<C>>(
    val collection: CallContext<*, T>,
    val phi: TFunction<Boolean>
) : TFunction<Collection<C>>

data class TFBranch<T>(
    val cond: TFunction<Boolean>,
    val thenFunction: TFunction<T>,
    val elseFunction: TFunction<T>
) : TFunction<T>
