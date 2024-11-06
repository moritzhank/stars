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

package tools.aqua.stars.logic.kcmftbl.dslFormulas

import tools.aqua.stars.logic.kcmftbl.dsl.times

class OvertakingPredicateExample {

  /*
  @Test
  fun monitors() {
    val onSameRoad = formula { v1: CCB<Vehicle>, v2: CCB<Vehicle> ->
      term(v1 * Vehicle::lane * Lane::road) eq term(v2 * Vehicle::lane * Lane::road)
    }
    val sameDirection = formula { v1: CCB<Vehicle>, v2: CCB<Vehicle> ->
      onSameRoad.holds(v1, v2) and
          (term(v1 * Vehicle::lane * Lane::laneId * Int::sign) eq
              term(v2 * Vehicle::lane * Lane::laneId * Int::sign))
    }
    val test = formula {
      exists { v1: CCB<Vehicle> ->
        v1.debugInfo = "v1"
        exists { v2: CCB<Vehicle> ->
          v2.debugInfo = "v2"
          sameDirection.holds(v1, v2)
        }
      }
    }
  }
   */
}
