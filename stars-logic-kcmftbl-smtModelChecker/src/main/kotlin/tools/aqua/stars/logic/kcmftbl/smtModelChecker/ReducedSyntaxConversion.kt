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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker

/*
fun toReducedSyntax(f: Formula, propagateNeg: Boolean = false): Formula {
  return when (f) {
    // Recursion anchor
    is FF,
    is TT -> if (propagateNeg) negAtomicAndCopy(f) else copyF(f)
    is Leq<*>,
    is Geq<*>,
    is Lt<*>,
    is Gt<*>,
    is Eq<*>,
    is Ne<*> -> if (propagateNeg) negRelationAndCopy(f) else copyF(f)
    // Reduced syntax
    is Neg -> toReducedSyntax(f.inner, !propagateNeg)
    is And ->
        if (propagateNeg) Or(toReducedSyntax(f.lhs, true), toReducedSyntax(f.rhs, true))
        else And(toReducedSyntax(f.lhs), toReducedSyntax(f.rhs))
    is Or ->
        if (propagateNeg) And(toReducedSyntax(f.lhs, true), toReducedSyntax(f.rhs, true))
        else Or(toReducedSyntax(f.lhs), toReducedSyntax(f.rhs))
    is Exists ->
        if (propagateNeg) Forall(toReducedSyntax(f.inner, true))
        else Exists(toReducedSyntax(f.inner))
    is Forall ->
        if (propagateNeg) Exists(toReducedSyntax(f.inner, true))
        else Forall(toReducedSyntax(f.inner))
    is Prev -> Prev(f.interval?.copy(), toReducedSyntax(f.inner)).wrapInNot(propagateNeg)
    is Next -> Next(f.interval?.copy(), toReducedSyntax(f.inner)).wrapInNot(propagateNeg)
    is Since ->
        Since(f.interval?.copy(), toReducedSyntax(f.lhs), toReducedSyntax(f.rhs))
            .wrapInNot(propagateNeg)
    is Until ->
        Until(f.interval?.copy(), toReducedSyntax(f.lhs), toReducedSyntax(f.rhs))
            .wrapInNot(propagateNeg)
    is MinPrevalence -> MinPrevalence(f.fraction, toReducedSyntax(f.inner)).wrapInNot(propagateNeg)
    is PastMinPrevalence ->
        PastMinPrevalence(f.fraction, toReducedSyntax(f.inner)).wrapInNot(propagateNeg)
    is Binding<*> -> Binding(copyT(f.bindTerm), toReducedSyntax(f.inner))
    // Beyond reduced syntax
    is Implication ->
        if (propagateNeg) And(toReducedSyntax(f.lhs), toReducedSyntax(f.rhs, true))
        else Or(toReducedSyntax(f.lhs, true), toReducedSyntax(f.rhs))
    is Iff ->
        if (propagateNeg)
            And(
                Or(toReducedSyntax(f.lhs, true), toReducedSyntax(f.rhs, true)),
                Or(toReducedSyntax(f.lhs), toReducedSyntax(f.rhs)))
        else
            Or(
                And(toReducedSyntax(f.lhs), toReducedSyntax(f.rhs)),
                And(toReducedSyntax(f.lhs, true), toReducedSyntax(f.rhs, true)))
    is Once -> Since(f.interval?.copy(), TT, toReducedSyntax(f.inner)).wrapInNot(propagateNeg)
    is Historically ->
        Since(f.interval?.copy(), TT, toReducedSyntax(f.inner, true)).wrapInNot(!propagateNeg)
    is Eventually -> Until(f.interval?.copy(), TT, toReducedSyntax(f.inner)).wrapInNot(propagateNeg)
    is Globally ->
        Until(f.interval?.copy(), TT, toReducedSyntax(f.inner, true)).wrapInNot(!propagateNeg)
    is MaxPrevalence ->
        MinPrevalence(1 - f.fraction, toReducedSyntax(f.inner, true)).wrapInNot(propagateNeg)
    is PastMaxPrevalence ->
        PastMinPrevalence(1 - f.fraction, toReducedSyntax(f.inner, true)).wrapInNot(propagateNeg)
  }
}

private fun negRelationAndCopy(f: Formula): Formula {
  return when (f) {
    is Leq<*> -> Gt(copyT(f.lhs), copyT(f.rhs))
    is Geq<*> -> Lt(copyT(f.lhs), copyT(f.rhs))
    is Lt<*> -> Geq(copyT(f.lhs), copyT(f.rhs))
    is Gt<*> -> Leq(copyT(f.lhs), copyT(f.rhs))
    is Eq<*> -> Ne(copyT(f.lhs), copyT(f.rhs))
    is Ne<*> -> Eq(copyT(f.lhs), copyT(f.rhs))
    else -> f
  }
}

private fun negAtomicAndCopy(f: Formula): Formula {
  return when (f) {
    is TT -> FF
    is FF -> TT
    else -> f
  }
}

private fun Formula.wrapInNot(wrapInNot: Boolean) = if (wrapInNot) Neg(this) else this
*/
