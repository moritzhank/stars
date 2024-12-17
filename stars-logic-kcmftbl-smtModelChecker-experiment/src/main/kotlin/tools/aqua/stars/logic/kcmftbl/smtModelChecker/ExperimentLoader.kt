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

import java.nio.file.Paths
import tools.aqua.stars.data.av.dataclasses.Segment
import tools.aqua.stars.importer.carla.CarlaSimulationRunsWrapper
import tools.aqua.stars.importer.carla.loadSegments

object ExperimentLoader {

  fun loadTestSegment(): Segment {
    val dynamic = getPathToResource("/data/dynamic_data__Game_Carla_Maps_Town01_seed2.json")
    val static = getPathToResource("/data/static_data__Game_Carla_Maps_Town01.json")
    val wrapper = CarlaSimulationRunsWrapper(static, listOf(dynamic))
    return loadSegments(listOf(wrapper), false, 10, true).first()
  }

  fun getPathToResource(name: String) =
      Paths.get(ExperimentLoader::class.java.getResource(name)!!.toURI())
}
