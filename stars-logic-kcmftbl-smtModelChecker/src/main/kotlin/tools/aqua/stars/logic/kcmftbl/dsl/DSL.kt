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

/*
class FormulaBuilder(val phi: MutableList<Formula> = mutableListOf()) {

  companion object {

    // formula with no free variables
    fun formula(init: FormulaBuilder.() -> Unit): Formula {
      val builder = FormulaBuilder()
      init.invoke(builder)
      return builder.phi[0]
    }

    // formula with one free variable (does not return formula!!)
    fun <
        E1 : E,
        E : EntityType<E, T, S, U, D>,
        T : TickDataType<E, T, S, U, D>,
        S : SegmentType<E, T, S, U, D>,
        U : TickUnit<U, D>,
        D : TickDifference<D>> formula(
        init: FormulaBuilder.(CallContextBase<E1>) -> Unit
    ): (CallContextBase<E1>) -> FormulaBuilder {
      return { ccb: CallContextBase<E1> ->
        val builder = FormulaBuilder()
        init.invoke(builder, ccb)
        builder
      }
    }

    // formula with two free variables of same EntityType (does not return formula!!)
    fun <
        E1 : E,
        E : EntityType<E, T, S, U, D>,
        T : TickDataType<E, T, S, U, D>,
        S : SegmentType<E, T, S, U, D>,
        U : TickUnit<U, D>,
        D : TickDifference<D>> formula(
        init: FormulaBuilder.(CallContextBase<E1>, CallContextBase<E1>) -> Unit
    ): (CallContextBase<E1>, CallContextBase<E1>) -> FormulaBuilder {
      return { ccb1: CallContextBase<E1>, ccb2: CallContextBase<E1> ->
        FormulaBuilder().apply { init(ccb1, ccb2) }.let { this }
        val builder = FormulaBuilder()
        init.invoke(builder, ccb1, ccb2)
        builder
      }
    }
  }

  /*
  // does formula with one variable hold for given variable
  fun <
      E1 : E,
      E : EntityType<E, T, S, U, D>,
      T : TickDataType<E, T, S, U, D>,
      S : SegmentType<E, T, S, U, D>,
      U : TickUnit<U, D>,
      D : TickDifference<D>> ((CallContextBase<E1>) -> FormulaBuilder).holds(
      ccb: CallContextBase<E1>
  ): Formula = this(ccb).phi[0].also { phi.add(it) }

  // does formula with two variables hold for given variables
  fun <
      E1 : E,
      E2 : E,
      E : EntityType<E, T, S, U, D>,
      T : TickDataType<E, T, S, U, D>,
      S : SegmentType<E, T, S, U, D>,
      U : TickUnit<U, D>,
      D : TickDifference<D>> ((CallContextBase<E1>, CallContextBase<E2>) -> FormulaBuilder).holds(
      ccb1: CallContextBase<E1>,
      ccb2: CallContextBase<E2>
  ): Formula = this(ccb1, ccb2).phi[0].also { phi.add(it) }
  */

  // region build formula elements (check number of passed sub formulae)
  private fun buildNeg(): Neg = assert(phi.size == 1).let { Neg(phi.first()) }

  private fun buildAnd(): And = assert(phi.size == 2).let { And(phi[0], phi[1]) }

  private fun buildOr(): Or = assert(phi.size == 2).let { Or(phi[0], phi[1]) }

  private fun buildImpl(): Implication = assert(phi.size == 2).let { Implication(phi[0], phi[1]) }

  private fun buildIff(): Iff = assert(phi.size == 2).let { Iff(phi[0], phi[1]) }

  private fun buildPrev(interval: Pair<Int, Int>?): Prev {
    assert(phi.size == 1)
    return Prev(interval, phi.first())
  }

  private fun buildNext(interval: Pair<Int, Int>?): Next {
    assert(phi.size == 1)
    return Next(interval, phi.first())
  }

  private fun buildOnce(interval: Pair<Int, Int>?): Once {
    assert(phi.size == 1)
    return Once(interval, phi.first())
  }

  private fun buildHistorically(interval: Pair<Int, Int>?): Historically {
    assert(phi.size == 1)
    return Historically(interval, phi.first())
  }

  private fun buildEventually(interval: Pair<Int, Int>?): Eventually {
    assert(phi.size == 1)
    return Eventually(interval, phi.first())
  }

  private fun buildAlways(interval: Pair<Int, Int>? = null): Always {
    assert(phi.size == 1)
    return Always(interval, inner = phi[0])
  }

  private fun buildSince(interval: Pair<Int, Int>? = null): Since {
    assert(phi.size == 2)
    return Since(interval, lhs = phi[0], rhs = phi[1])
  }

  private fun buildUntil(interval: Pair<Int, Int>? = null): Until {
    assert(phi.size == 2)
    return Until(interval, lhs = phi[0], rhs = phi[1])
  }
  // todo: rework
  fun <
      E1 : E,
      E : EntityType<E, T, S, U, D>,
      T : TickDataType<E, T, S, U, D>,
      S : SegmentType<E, T, S, U, D>,
      U : TickUnit<U, D>,
      D : TickDifference<D>> buildForall(ccb: CallContextBase<E1>): Forall<E1> {
    assert(phi.size == 1)
    return Forall(ccb, phi[0])
  }
  // todo: rework
  fun <
      E1 : E,
      E : EntityType<E, T, S, U, D>,
      T : TickDataType<E, T, S, U, D>,
      S : SegmentType<E, T, S, U, D>,
      U : TickUnit<U, D>,
      D : TickDifference<D>> buildExists(ccb: CallContextBase<E1>): Exists<E1> {
    assert(phi.size == 1)
    return Exists(ccb, phi[0])
  }

  private fun buildMinPrevalence(fraction: Double): MinPrevalence {
    assert(phi.size == 1)
    return MinPrevalence(fraction, phi[0])
  }

  private fun buildMaxPrevalence(fraction: Double): MaxPrevalence {
    assert(phi.size == 1)
    return MaxPrevalence(fraction, phi[0])
  }

  private fun buildPastMinPrevalence(fraction: Double): PastMinPrevalence {
    assert(phi.size == 1)
    return PastMinPrevalence(fraction, phi[0])
  }

  private fun buildPastMaxPrevalence(fraction: Double): PastMaxPrevalence {
    assert(phi.size == 1)
    return PastMaxPrevalence(fraction, phi[0])
  }

  private fun <Type> buildBinding(ccb: CallContextBase<Type>, term: Term<Type>): Binding<Type> {
    assert(phi.size == 1)
    return Binding(ccb, term, phi[0])
  }
  // endregion

  // region formula definitions
  fun FormulaBuilder.tt(): TT = TT.also { phi.add(it) }

  fun FormulaBuilder.ff(): FF = FF.also { phi.add(it) }
  // todo: rework
  /*
  fun <
      E1 : E,
      E : EntityType<E, T, S, U, D>,
      T : TickDataType<E, T, S, U, D>,
      S : SegmentType<E, T, S, U, D>,
      U : TickUnit<U, D>,
      D : TickDifference<D>> FormulaBuilder.pred(
      ccb: CallContextBase<E1>,
      init: () -> Boolean = { true }
  ): Formula = UnaryPredicate(ccb, init).also { phi.add(it) }
  fun <
      E1 : E,
      E2 : E,
      E : EntityType<E, T, S, U, D>,
      T : TickDataType<E, T, S, U, D>,
      S : SegmentType<E, T, S, U, D>,
      U : TickUnit<U, D>,
      D : TickDifference<D>> FormulaBuilder.pred(
      ccb1: CallContextBase<E1>,
      ccb2: CallContextBase<E2>,
      init: () -> Boolean = { true }
  ): Formula = BinaryPredicate(ccb1, ccb2, init).also { phi.add(it) }
  */
  fun FormulaBuilder.neg(input: Formula): Neg {
    return Neg(input).also { phi.add(it) }
  }

  fun FormulaBuilder.neg(init: FormulaBuilder.() -> Unit = {}): Neg {
    return FormulaBuilder().apply(init).buildNeg().also { phi.add(it) }
  }

  infix fun Formula.and(other: Formula): And =
      And(this, other).also {
        phi.removeLast()
        phi.removeLast()
        phi.add(it)
      }

  infix fun Formula.or(other: Formula): Or =
      Or(this, other).also {
        phi.clear()
        phi.add(it)
      }

  infix fun Formula.impl(other: Formula): Implication =
      Implication(this, other).also {
        phi.clear()
        phi.add(it)
      }

  infix fun Formula.iff(other: Formula): Iff =
      Iff(this, other).also {
        phi.clear()
        phi.add(it)
      }

  fun FormulaBuilder.prev(
      interval: Pair<Int, Int>? = null,
      init: FormulaBuilder.() -> Unit = {}
  ): Prev {
    return FormulaBuilder().apply(init).buildPrev(interval).also { phi.add(it) }
  }

  fun FormulaBuilder.next(
      interval: Pair<Int, Int>? = null,
      init: FormulaBuilder.() -> Unit = {}
  ): Next {
    return FormulaBuilder().apply(init).buildNext(interval).also { phi.add(it) }
  }

  fun FormulaBuilder.once(
      interval: Pair<Int, Int>? = null,
      init: FormulaBuilder.() -> Unit = {}
  ): Once {
    return FormulaBuilder().apply(init).buildOnce(interval).also { phi.add(it) }
  }

  fun FormulaBuilder.historically(
      interval: Pair<Int, Int>? = null,
      init: FormulaBuilder.() -> Unit = {}
  ): Historically {
    return FormulaBuilder().apply(init).buildHistorically(interval).also { phi.add(it) }
  }

  fun eventually(
      interval: Pair<Int, Int>? = null,
      init: FormulaBuilder.() -> Unit = {}
  ): Eventually {
    return FormulaBuilder().apply(init).buildEventually(interval).also { phi.add(it) }
  }

  fun FormulaBuilder.always(
      interval: Pair<Int, Int>? = null,
      init: FormulaBuilder.() -> Unit = {}
  ): Always {
    return FormulaBuilder().apply(init).buildAlways(interval).also { phi.add(it) }
  }

  fun FormulaBuilder.since(
      interval: Pair<Int, Int>? = null,
      init: FormulaBuilder.() -> Unit = {}
  ): Since {
    return FormulaBuilder().apply(init).buildSince(interval).also { phi.add(it) }
  }

  fun FormulaBuilder.until(
      interval: Pair<Int, Int>? = null,
      init: FormulaBuilder.() -> Unit = {}
  ): Until {
    return FormulaBuilder().apply(init).buildUntil(interval).also { phi.add(it) }
  }

  inline fun <
      reified E1 : E,
      E : EntityType<E, T, S, U, D>,
      T : TickDataType<E, T, S, U, D>,
      S : SegmentType<E, T, S, U, D>,
      U : TickUnit<U, D>,
      D : TickDifference<D>> FormulaBuilder.forall(
      init: FormulaBuilder.(CallContextBase<E1>) -> Unit = {}
  ): Forall<E1> {
    val ccb = CallContextBase<E1>()
    return FormulaBuilder().apply { init(ccb) }.buildForall(ccb).also { phi.add(it) }
  }

  inline fun <
      reified E1 : E,
      E : EntityType<E, T, S, U, D>,
      T : TickDataType<E, T, S, U, D>,
      S : SegmentType<E, T, S, U, D>,
      U : TickUnit<U, D>,
      D : TickDifference<D>> FormulaBuilder.exists(
      init: FormulaBuilder.(CallContextBase<E1>) -> Unit = {}
  ): Exists<E1> {
    val ccb = CallContextBase<E1>()
    return FormulaBuilder().apply { init(ccb) }.buildExists(ccb).also { phi.add(it) }
  }

  fun FormulaBuilder.minPrevalence(
      fraction: Double,
      init: FormulaBuilder.() -> Unit = {}
  ): MinPrevalence {
    return FormulaBuilder().apply(init).buildMinPrevalence(fraction).also { phi.add(it) }
  }

  fun FormulaBuilder.maxPrevalence(
      fraction: Double,
      init: FormulaBuilder.() -> Unit = {}
  ): MaxPrevalence {
    return FormulaBuilder().apply(init).buildMaxPrevalence(fraction).also { phi.add(it) }
  }

  fun FormulaBuilder.pastMinPrevalence(
      fraction: Double,
      init: FormulaBuilder.() -> Unit = {}
  ): PastMinPrevalence {
    return FormulaBuilder().apply(init).buildPastMinPrevalence(fraction).also { phi.add(it) }
  }

  fun FormulaBuilder.pastMaxPrevalence(
      fraction: Double,
      init: FormulaBuilder.() -> Unit = {}
  ): PastMaxPrevalence {
    return FormulaBuilder().apply(init).buildPastMaxPrevalence(fraction).also { phi.add(it) }
  }

  fun <Type> FormulaBuilder.binding(
      term: Term<Type>,
      init: FormulaBuilder.(CallContextBase<Type>) -> Unit = {}
  ): Binding<Type> {
    val ccb = CallContextBase<Type>()
    return FormulaBuilder().apply { init(ccb) }.buildBinding(ccb, term).also { phi.add(it) }
  }

  infix fun <Type> Term<Type>.leq(other: Term<Type>): Leq<Type> =
      Leq(this, other).also { phi.add(it) }

  infix fun <Type> Term<Type>.lt(other: Term<Type>): Lt<Type> = Lt(this, other).also { phi.add(it) }

  infix fun <Type> Term<Type>.geq(other: Term<Type>): Geq<Type> =
      Geq(this, other).also { phi.add(it) }

  infix fun <Type> Term<Type>.gt(other: Term<Type>): Gt<Type> = Gt(this, other).also { phi.add(it) }

  infix fun <Type> Term<Type>.eq(other: Term<Type>): Eq<Type> = Eq(this, other).also { phi.add(it) }

  infix fun <Type> Term<Type>.ne(other: Term<Type>): Ne<Type> = Ne(this, other).also { phi.add(it) }

  fun <Type> term(ccb: CallContext<*, Type>): Variable<Type> = Variable(ccb)

  fun <Type> const(value: Type): Constant<Type> = Constant(value)
  // endregion
}

/*
// holds
fun <
    E1 : E,
    E : EntityType<E, T, S, U, D>,
    T : TickDataType<E, T, S, U, D>,
    S : SegmentType<E, T, S, U, D>,
    U : TickUnit<U, D>,
    D : TickDifference<D>> ((Ref<E1>) -> FormulaBuilder).holds(ref1: Ref<E1>): Formula =
    this(ref1).phi[0]

fun <
    E1 : E,
    E2 : E,
    E : EntityType<E, T, S, U, D>,
    T : TickDataType<E, T, S, U, D>,
    S : SegmentType<E, T, S, U, D>,
    U : TickUnit<U, D>,
    D : TickDifference<D>> ((Ref<E1>, Ref<E2>) -> FormulaBuilder).holds(
    ref1: Ref<E1>,
    ref2: Ref<E2>
): Formula = this(ref1, ref2).phi[0]
*/
 */
