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

import java.io.File
import java.net.URI
import java.net.URLEncoder
import java.util.UUID
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.getAbsolutePathFromProjectDir

/** Translate a given formula into Latex. */
fun formulaToLatex(fBuilder: FormulaBuilder): String {
  val phi = fBuilder.getPhi().first()
  return phi.str()
}

/** Generate an SVG of the input formula. */
fun renderLatexFormula(latex: String, deletePrevSvgs: Boolean = true) {
  val formulaImgs = getAbsolutePathFromProjectDir("formulaSvgs")
  File(formulaImgs)
      .apply {
        if (deletePrevSvgs) {
          deleteRecursively()
        }
      }
      .mkdir()
  val encodedLatex = URLEncoder.encode(latex, "utf-8")
  val url = URI("https://math.vercel.app?from=$encodedLatex").toURL()
  val imageData = url.readBytes()
  val imageFilePath = "$formulaImgs${File.separator}${UUID.randomUUID()}.svg"
  File(imageFilePath).apply { writeBytes(imageData) }
}

private fun Formula.str(): String {
  val f = this
  return when (f) {
    is Always -> "□_{${f.interval.str()}}(${f.inner.str()})"
    is And -> "(${f.lhs.str()})\\land (${f.rhs.str()})"
    is Binding<*> -> "↓_${f.ccb.str()}^{${f.bindTerm.str()}}(${f.inner.str()})"
    is Eq<*> -> "${f.lhs.str()}=${f.rhs.str()}"
    is Eventually -> "♢_{${f.interval.str()}}(${f.inner.str()})"
    is Exists<*> -> "\\exists ${f.ccb.str()}:(${f.inner.str()})"
    FF -> "\\bot "
    is Forall<*> -> "\\forall ${f.ccb.str()}:(${f.inner.str()})"
    is Geq<*> -> "${f.lhs.str()}\\geq ${f.rhs.str()}"
    is Gt<*> -> "${f.lhs.str()}\\gt ${f.rhs.str()}"
    is Historically -> "■_{${f.interval.str()}}(${f.inner.str()})"
    is Iff -> "(${f.lhs.str()})\\Leftrightarrow (${f.rhs.str()})"
    is Implication -> "(${f.lhs.str()})\\Rightarrow (${f.rhs.str()})"
    is Leq<*> -> "${f.lhs.str()}\\leq ${f.rhs.str()}"
    is Lt<*> -> "${f.lhs.str()}\\lt ${f.rhs.str()}"
    is MaxPrevalence -> "△_{${f.interval.str()}}^{${f.fraction}}(${f.inner.str()})"
    is MinPrevalence -> "▽_{${f.interval.str()}}^{${f.fraction}}(${f.inner.str()})"
    is Ne<*> -> "${f.lhs.str()}\\neq ${f.rhs.str()}"
    is Neg -> "\\neg (${f.inner.str()})"
    is Next -> "○_{${f.interval.str()}}(${f.inner.str()})"
    is Once -> "♦_{${f.interval.str()}}(${f.inner.str()})"
    is Or -> "(${f.lhs.str()})\\lor (${f.rhs.str()})"
    is PastMaxPrevalence -> "▲_{${f.interval.str()}}^{${f.fraction}}(${f.inner.str()})"
    is PastMinPrevalence -> "▼_{${f.interval.str()}}^{${f.fraction}}(${f.inner.str()})"
    is Prev -> "●_{${f.interval.str()}}(${f.inner.str()})"
    is Since -> "(${f.lhs.str()}) \\mathcal{S}_{${f.interval.str()}} (${f.rhs.str()})"
    TT -> "\\top "
    is Until -> "(${f.lhs.str()}) \\mathcal{U}_{${f.interval.str()}} (${f.rhs.str()})"
  }
}

private fun Term<*>.str(): String {
  val t = this
  return when (t) {
    is Constant -> t.value.toString()
    is Variable -> t.callContext.str()
  }
}

private fun CallContext<*, *>.str(tmp: String? = null): String {
  val cc = this
  val _tmp = if (tmp == null) "" else ".$tmp"
  return when (cc) {
    is CallContextBase -> "$cc$_tmp"
    is Callable1CallContext -> cc.before!!.str("${cc.func.name}()$_tmp")
    is Callable2CallContext<*, *, *> -> cc.before!!.str("${cc.func.name}(${cc.param.str()})$_tmp")
    is Callable3CallContext<*, *, *, *> ->
        cc.before!!.str("${cc.func.name}(${cc.param1.str()},${cc.param2.str()})$_tmp")
    is PropertyCallContext -> cc.before!!.str("${cc.prop.name}$_tmp")
  }
}

private fun Pair<Int, Int>?.str(): String = if (this == null) "[0,∞)" else "[$first,$second]"
