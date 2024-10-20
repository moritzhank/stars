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

import tools.aqua.stars.core.types.EntityType

sealed interface Formula

data object TT : Formula

data object FF : Formula

data class Neg(val inner: Formula) : Formula

data class And(val lhs: Formula, val rhs: Formula) : Formula

data class Or(val lhs: Formula, val rhs: Formula) : Formula

data class Implication(val lhs: Formula, val rhs: Formula) : Formula

data class Iff(val lhs: Formula, val rhs: Formula) : Formula

data class Prev(val interval: Pair<Int, Int>? = null, val inner: Formula) : Formula

data class Next(val interval: Pair<Int, Int>? = null, val inner: Formula) : Formula

data class Once(val interval: Pair<Int, Int>? = null, val inner: Formula) : Formula

data class Historically(val interval: Pair<Int, Int>? = null, val inner: Formula) : Formula

data class Eventually(val interval: Pair<Int, Int>? = null, val inner: Formula) : Formula

data class Always(val interval: Pair<Int, Int>? = null, val inner: Formula) : Formula

data class Since(val interval: Pair<Int, Int>? = null, val lhs: Formula, val rhs: Formula) :
    Formula

data class Until(val interval: Pair<Int, Int>? = null, val lhs: Formula, val rhs: Formula) :
    Formula

data class Forall<E : EntityType<*, *, *, *, *>>(val ccb: CallContextBase<E>, val inner: Formula) :
    Formula

data class Exists<E : EntityType<*, *, *, *, *>>(val ccb: CallContextBase<E>, val inner: Formula) :
    Formula

data class Binding<Type>(
    val ccb: CallContextBase<Type>,
    val bindTerm: Term<Type>,
    val inner: Formula
) : Formula {

  fun copy(): Binding<Type> = Binding(ccb, copyTerm(bindTerm), inner)
}

data class MinPrevalence(val fraction: Double, val inner: Formula) : Formula

data class PastMinPrevalence(val fraction: Double, val inner: Formula) : Formula

data class MaxPrevalence(val fraction: Double, val inner: Formula) : Formula

data class PastMaxPrevalence(val fraction: Double, val inner: Formula) : Formula

/** Create a deep copy of [formula] */
fun copyFormula(formula: Formula): Formula {
  return when (formula) {
    is TT -> formula
    is FF -> formula
    is Neg -> Neg(copyFormula(formula.inner))
    is And -> And(copyFormula(formula.lhs), copyFormula(formula.rhs))
    is Or -> Or(copyFormula(formula.lhs), copyFormula(formula.rhs))
    is Implication -> Implication(copyFormula(formula.lhs), copyFormula(formula.rhs))
    is Iff -> Iff(copyFormula(formula.lhs), copyFormula(formula.rhs))
    is Prev -> Prev(formula.interval?.copy(), copyFormula(formula.inner))
    is Next -> Next(formula.interval?.copy(), copyFormula(formula.inner))
    is Once -> Once(formula.interval?.copy(), copyFormula(formula.inner))
    is Historically -> Historically(formula.interval?.copy(), copyFormula(formula.inner))
    is Eventually -> Eventually(formula.interval?.copy(), copyFormula(formula.inner))
    is Always -> Always(formula.interval?.copy(), copyFormula(formula.inner))
    is Since -> Since(formula.interval?.copy(), copyFormula(formula.lhs), copyFormula(formula.rhs))
    is Until -> Until(formula.interval?.copy(), copyFormula(formula.lhs), copyFormula(formula.rhs))
    is Forall<*> -> Forall(formula.ccb, copyFormula(formula.inner))
    is Exists<*> -> Exists(formula.ccb, copyFormula(formula.inner))
    is Binding<*> -> formula.copy()
    is MinPrevalence -> MinPrevalence(formula.fraction, copyFormula(formula.inner))
    is PastMinPrevalence -> PastMinPrevalence(formula.fraction, copyFormula(formula.inner))
    is MaxPrevalence -> MaxPrevalence(formula.fraction, copyFormula(formula.inner))
    is PastMaxPrevalence -> PastMaxPrevalence(formula.fraction, copyFormula(formula.inner))
    is Leq<*> -> formula.copy()
    is Geq<*> -> formula.copy()
    is Lt<*> -> formula.copy()
    is Gt<*> -> formula.copy()
    is Eq<*> -> formula.copy()
    is Ne<*> -> formula.copy()
  }
}
