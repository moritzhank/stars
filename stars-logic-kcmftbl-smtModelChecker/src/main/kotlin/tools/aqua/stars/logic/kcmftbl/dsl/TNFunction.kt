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

/** Symbolic representation of n-ary functions (Wraps [TFunction]) */
sealed interface TNFunction<Return> {
  val func: TFunction<Return>
}

sealed interface T1Function<Return> : TNFunction<Return>

sealed interface T2Function<Param, Return> : TNFunction<Return>

sealed interface T3Function<Param1, Param2, Return> : TNFunction<Return>

sealed interface T4Function<Param1, Param2, Param3, Return> : TNFunction<Return>
