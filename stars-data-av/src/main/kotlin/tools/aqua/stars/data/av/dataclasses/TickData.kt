/*
 * Copyright 2023-2025 The STARS Project Authors
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

package tools.aqua.stars.data.av.dataclasses

import kotlinx.serialization.Serializable
import tools.aqua.stars.core.types.TickDataType
import tools.aqua.stars.data.av.serializer.TickDataSerializer
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.SmtTranslatableBase
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.encoding.SmtAllowNonTrivialGetter

/**
 * Json format containing data for current tick.
 *
 * @property currentTick Current tick value.
 * @property entities List of all [Actor]s.
 * @property trafficLights List of all [TrafficLight]s.
 * @property blocks ist of all [Block]s.
 * @property weather The current [WeatherParameters].
 * @property daytime The current [Daytime].
 */
@Serializable(with = TickDataSerializer::class)
data class TickData(
    override val currentTick: TickDataUnitSeconds,
    override var entities: List<Actor>,
    val trafficLights: List<TrafficLight>,
    val blocks: List<Block>,
    val weather: WeatherParameters,
    val daytime: Daytime
) :
    SmtTranslatableBase(),
    TickDataType<Actor, TickData, Segment, TickDataUnitSeconds, TickDataDifferenceSeconds> {

  override lateinit var segment: Segment

  /** Name-Alias for [entities]. */
  val actors: List<Actor>
    get() = entities

  /** The ego vehicle. */
  val egoVehicle: Vehicle
    get() = actors.firstOrNull { it is Vehicle && it.isEgo } as Vehicle

  /** All vehicles. */
  @SmtAllowNonTrivialGetter
  val vehicles: List<Vehicle>
    get() = actors.filterIsInstance<Vehicle>()

  /** All pedestrians. */
  @Suppress("unused")
  @SmtAllowNonTrivialGetter
  val pedestrians: List<Pedestrian>
    get() = actors.filterIsInstance<Pedestrian>()

  /** Returns [Actor] with given [actorID]. */
  fun actor(actorID: Int): Actor? = actors.firstOrNull { it.id == actorID }

  /** Returns all [Vehicle]s in given [Block]. */
  fun vehiclesInBlock(block: Block): List<Vehicle> = vehicles.filter { it.lane.road.block == block }

  /** Clones current [TickData]. */
  fun clone(): TickData {
    val newTickData = TickData(currentTick, emptyList(), trafficLights, blocks, weather, daytime)
    newTickData.entities = actors.map { it.clone(newTickData) }
    return newTickData
  }

  override fun toString(): String = "$currentTick"
}
