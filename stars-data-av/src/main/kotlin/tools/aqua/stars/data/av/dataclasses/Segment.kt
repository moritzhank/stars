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
import kotlinx.serialization.Transient
import tools.aqua.stars.core.types.SegmentType
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.dataTranslation.SmtTranslatableBase

/**
 * Evaluation segment.
 *
 * @property mainInitList [TickData] of the [Segment].
 * @property simulationRunId Identifier of the simulation run.
 * @property segmentSource Source identifier.
 */
@Serializable
data class Segment(
    val mainInitList: List<TickData>,
    val simulationRunId: String = "",
    override val segmentSource: String,
) :
    SmtTranslatableBase(),
    SegmentType<Actor, TickData, Segment, TickDataUnitSeconds, TickDataDifferenceSeconds> {

  override val tickData: List<TickData> = mainInitList.onEach { it.segment = this }

  @Transient
  override val ticks: Map<TickDataUnitSeconds, TickData> = tickData.associateBy { it.currentTick }

  override val primaryEntityId: Int
    get() {
      val firstTick = tickData.first()
      check(firstTick.entities.filterIsInstance<Vehicle>().any { it.isEgo }) {
        "There is no primary entity for tick $firstTick"
      }
      val firstEgo = firstTick.egoVehicle
      check(tickData.any { it.entities.filterIsInstance<Vehicle>().count { v -> v.isEgo } == 1 }) {
        "There is at least one tick with multiple primary entities in segment ${this.toString(firstEgo.id)}"
      }
      if (tickData.any { it.egoVehicle.id != firstEgo.id })
          error("The ego id changes in Segment ${this.toString(firstEgo.id)}")
      return firstEgo.id
    }

  /** Cache for all vehicle IDs. */
  @Transient private val vehicleIdsCache = mutableListOf<Int>()

  /** All vehicle IDs of the segment. */
  val vehicleIds: List<Int>
    get() {
      if (vehicleIdsCache.isEmpty()) {
        vehicleIdsCache.addAll(
            tickData
                .flatMap { tickData -> tickData.entities.filterIsInstance<Vehicle>().map { it.id } }
                .distinct())
      }
      return vehicleIdsCache
    }

  /** Cache for all pedestrian IDs. */
  @Transient private val pedestrianIdsCache = mutableListOf<Int>()

  /** All pedestrian IDs of the segment. */
  @Suppress("unused")
  val pedestrianIds: List<Int>
    get() {
      if (pedestrianIdsCache.isEmpty()) {
        pedestrianIdsCache.addAll(
            tickData
                .flatMap { tickData ->
                  tickData.entities.filterIsInstance<Pedestrian>().map { it.id }
                }
                .distinct())
      }
      return pedestrianIdsCache
    }

  /**
   * Converts segment to String representation including [tickData] range and given [egoId].
   *
   * @param egoId Identifier of the ego vehicle to be included.
   */
  fun toString(egoId: Int): String =
      "Segment[(${tickData.first().currentTick}..${tickData.last().currentTick})] from $simulationRunId " +
          "with ego $egoId"

  override fun toString(): String = toString(this.primaryEntityId)

  override fun equals(other: Any?): Boolean {
    if (other is Segment) {
      return simulationRunId == other.simulationRunId &&
          segmentSource == other.segmentSource &&
          primaryEntityId == other.primaryEntityId &&
          tickData == other.tickData
    }
    return super.equals(other)
  }

  override fun hashCode(): Int = this.toString().hashCode()
}
