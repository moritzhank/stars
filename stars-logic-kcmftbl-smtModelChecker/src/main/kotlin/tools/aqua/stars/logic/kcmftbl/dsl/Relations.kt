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

data class Leq<Type>(val lhs: Term<Type>, val rhs: Term<Type>) : Formula {

  fun copy(): Leq<Type> = Leq(copyTerm(lhs), copyTerm(rhs))
}

data class Geq<Type>(val lhs: Term<Type>, val rhs: Term<Type>) : Formula {

  fun copy(): Geq<Type> = Geq(copyTerm(lhs), copyTerm(rhs))
}

data class Lt<Type>(val lhs: Term<Type>, val rhs: Term<Type>) : Formula {

  fun copy(): Lt<Type> = Lt(copyTerm(lhs), copyTerm(rhs))
}

data class Gt<Type>(val lhs: Term<Type>, val rhs: Term<Type>) : Formula {

  fun copy(): Gt<Type> = Gt(copyTerm(lhs), copyTerm(rhs))
}

data class Eq<Type>(val lhs: Term<Type>, val rhs: Term<Type>) : Formula {

  fun copy(): Eq<Type> = Eq(copyTerm(lhs), copyTerm(rhs))
}

data class Ne<Type>(val lhs: Term<Type>, val rhs: Term<Type>) : Formula {

  fun copy(): Ne<Type> = Ne(copyTerm(lhs), copyTerm(rhs))
}

enum class Relation {
  Leq,
  Geq,
  Lt,
  Gt,
  Eq,
  Ne
}
