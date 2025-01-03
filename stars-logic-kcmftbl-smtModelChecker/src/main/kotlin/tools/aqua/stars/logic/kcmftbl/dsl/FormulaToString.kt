/*
 * Copyright 2025 The STARS Project Authors
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

/** Translate a given formula into a String. */
fun formulaToString(fBuilder: FormulaBuilder): String {
  val phi = fBuilder.getPhi().first()
  return phi.str()
}

private fun Formula.str(): String {
  val f = this
  return when (f) {
    is Always -> "□_${f.interval.str()}(${f.inner.str()})"
    is And -> "(${f.lhs.str()})∧(${f.rhs.str()})"
    is Binding<*> -> "↓_${f.ccb.str()}^${f.bindTerm.str()}(${f.inner.str()})"
    is Eq<*> -> "${f.lhs.str()}=${f.rhs.str()}"
    is Eventually -> "♢_${f.interval.str()}(${f.inner.str()})"
    is Exists<*> -> "∃${f.ccb.str()}:${f.inner.str()}"
    FF -> "⊥"
    is Forall<*> -> "∀${f.ccb.str()}:${f.inner.str()}"
    is Geq<*> -> "${f.lhs.str()}≥${f.rhs.str()}"
    is Gt<*> -> "${f.lhs.str()}>${f.rhs.str()}"
    is Historically -> "■_${f.interval.str()}(${f.inner.str()})"
    is Iff -> "(${f.lhs.str()})⇔(${f.rhs.str()})"
    is Implication -> "(${f.lhs.str()})⇒(${f.rhs.str()})"
    is Leq<*> -> "${f.lhs.str()}≤${f.rhs.str()}"
    is Lt<*> -> "${f.lhs.str()}<${f.rhs.str()}"
    is MaxPrevalence -> "△_${f.interval.str()}^${f.fraction}(${f.inner.str()})"
    is MinPrevalence -> "▽_${f.interval.str()}^${f.fraction}(${f.inner.str()})"
    is Ne<*> -> "${f.lhs.str()}≠${f.rhs.str()}"
    is Neg -> "¬(${f.inner.str()})"
    is Next -> "○_${f.interval.str()}(${f.inner.str()})"
    is Once -> "♦_${f.interval.str()}(${f.inner.str()})"
    is Or -> "(${f.lhs.str()})∨(${f.rhs.str()})"
    is PastMaxPrevalence -> "▲_${f.interval.str()}^${f.fraction}(${f.inner.str()})"
    is PastMinPrevalence -> "▼_${f.interval.str()}^${f.fraction}(${f.inner.str()})"
    is Prev -> "●_${f.interval.str()}(${f.inner.str()})"
    is Since -> "(${f.lhs.str()}) S_${f.interval.str()} (${f.rhs.str()})"
    TT -> "⊤"
    is Until -> "(${f.lhs.str()}) U_${f.interval.str()} (${f.rhs.str()})"
  }
}

private fun Term<*>.str(): String {
  val t = this
  return when (t) {
    is Constant -> t.value.toString()
    is Variable -> t.callContext.str()
  }
}

private fun CallContext<*, *>.str(tmp: String = ""): String {
  val cc = this
  return when (cc) {
    is CallContextBase -> "$cc.$tmp"
    is Callable1CallContext -> cc.before!!.str("${cc.func.name}().$tmp")
    is Callable2CallContext<*, *, *> -> cc.before!!.str("${cc.func.name}(${cc.param.str()}).$tmp")
    is Callable3CallContext<*, *, *, *> ->
        cc.before!!.str("${cc.func.name}(${cc.param1.str()},${cc.param2.str()}).$tmp")
    is PropertyCallContext -> cc.before!!.str("${cc.prop.name}.$tmp")
  }
}

private fun Pair<Int, Int>?.str(): String = if (this == null) "[0,∞)" else "[$first,$second]"
