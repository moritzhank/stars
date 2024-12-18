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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.experiments

import tools.aqua.stars.data.av.dataclasses.*
import tools.aqua.stars.logic.kcmftbl.dsl.CCB
import tools.aqua.stars.logic.kcmftbl.dsl.FormulaBuilder.Companion.formula
import tools.aqua.stars.logic.kcmftbl.dsl.TFunctionBuilder.Companion.function
import tools.aqua.stars.logic.kcmftbl.dsl.times

fun main() {
  val vehiclesInBlock = function { t: CCB<TickData>, b: CCB<Block> ->
    filter(t * TickData::vehicles) { v: CCB<Vehicle> ->
      eq {
        wrap(v * Vehicle::lane * Lane::road * Road::block)
        wrap(b)
      }
    }
  }
  /*
  Original formula formulation:
  val hasMidTrafficDensity = predicate(Vehicle::class) { _, v ->
      minPrevalence(v, 0.6) { v -> v.tickData.vehiclesInBlock(v.lane.road.block).size in 6..15
  }
  */
  val hasMidTrafficDensity = formula { v: CCB<Vehicle> ->
    registerFunction(TickData::vehiclesInBlock, vehiclesInBlock)
    minPrevalence(0.6) {
      val x1 = v * Vehicle::tickData
      val x2 = x1 * TickData::vehiclesInBlock
      val x3 = x2.withParam(v * Vehicle::lane * Lane::road * Road::block)

      val term1 = term(x3 * List<Vehicle>::size)
      val term2 =
          term(
              (v * Vehicle::tickData * TickData::vehiclesInBlock).withParam(
                  v * Vehicle::lane * Lane::road * Road::block) * List<Vehicle>::size)
      const(6) leq term1 and (term2 leq const(15))
    }
  }
  val ccb = CCB<Vehicle>().apply { debugInfo = "v" }
  val ast = hasMidTrafficDensity(ccb)
}
