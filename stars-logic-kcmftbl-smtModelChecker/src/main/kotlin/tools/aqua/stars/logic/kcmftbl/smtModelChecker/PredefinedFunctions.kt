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

import tools.aqua.stars.logic.kcmftbl.dsl.CCB
import tools.aqua.stars.logic.kcmftbl.dsl.TFunctionBuilder.Companion.function

sealed class PredefinedFunctions {

  companion object {

    val IntSignFunction = function { int: CCB<Int> ->
      branch {
            eq {
              wrap(int)
              const(0)
            }
          }
          .satisfied { const(10) }
          .otherwise {
            branch {
                  gt {
                    wrap(int)
                    const(0)
                  }
                }
                .satisfied { const(1) }
                .otherwise { const(-1) }
          }
    }
  }
}