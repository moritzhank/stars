/*
 * Copyright 2023 The STARS Project Authors
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

package tools.aqua.stars.core.metric.metrics.postEvaluation

import java.util.logging.Logger
import tools.aqua.stars.core.evaluation.PredicateCombination
import tools.aqua.stars.core.metric.metrics.evaluation.ValidTSCInstancesPerProjectionMetric
import tools.aqua.stars.core.metric.providers.Loggable
import tools.aqua.stars.core.metric.providers.PostEvaluationMetricProvider
import tools.aqua.stars.core.tsc.*
import tools.aqua.stars.core.types.EntityType
import tools.aqua.stars.core.types.SegmentType
import tools.aqua.stars.core.types.TickDataType

/**
 * This class implements the [PostEvaluationMetricProvider] and calculates all missing
 * [PredicateCombination]s for all [TSCProjection]s.
 *
 * This class implements the [Loggable] interface. It logs and prints the count of missing
 * [PredicateCombination]s for each [TSCProjection]. It logs the missing [PredicateCombination]s for
 * each [TSCProjection].
 */
class MissingPredicateCombinationsPerProjectionMetric<
    E : EntityType<E, T, S>, T : TickDataType<E, T, S>, S : SegmentType<E, T, S>>(
    override val dependsOn: ValidTSCInstancesPerProjectionMetric<E, T, S>,
    override val logger: Logger = Loggable.getLogger("missing-predicate-combinations")
) : PostEvaluationMetricProvider<E, T, S>, Loggable {

  /**
   * Returns a [Set] of all missing [PredicateCombination]s for all [TSCProjection]s that are
   * calculated by the [ValidTSCInstancesPerProjectionMetric].
   */
  override fun evaluate(): Map<TSCProjection<E, T, S>, Set<PredicateCombination>> {
    return dependsOn.getState().mapValues {
      getAllMissingPredicateCombinationsForProjection(it.key, it.value.map { it.key })
    }
  }

  /**
   * Prints the count of missed [PredicateCombination]s for each [TSCProjection] and then the actual
   * list of the missed predicates
   */
  override fun print() {
    val evaluationResult = evaluate()
    evaluationResult.forEach { (projection, missedPredicates) ->
      logInfo(
          "Count of missing predicate combinations for projection '$projection': ${missedPredicates.size}.")
      missedPredicates
          .sortedWith(compareBy<PredicateCombination> { it.predicate1 }.thenBy { it.predicate2 })
          .forEach { logFine(it) }
      logFine()
    }
  }

  /**
   * Calculate the [Set] of [PredicateCombination]s that are missing.
   *
   * @param tscProjection The [TSCProjection] for which the missing [PredicateCombination]s should
   * be calculated
   * @param tscInstances The occurred [List] of [TSCInstanceNode]s
   *
   * @return A [Set] of [PredicateCombination]s that can occur based on the given [tscProjection]
   * but are not present in the given [tscInstances]
   */
  private fun getAllMissingPredicateCombinationsForProjection(
      tscProjection: TSCProjection<E, T, S>,
      tscInstances: List<TSCInstanceNode<E, T, S>>
  ): Set<PredicateCombination> {
    // Get all possible predicate combinations
    val projectionPossiblePredicateCombinations =
        getAllPredicateCombinations(tscProjection.possibleTSCInstances)
    // Get all occurred predicate combinations
    val occurredPredicateCombinations = getAllPredicateCombinations(tscInstances)
    // Return predicate combinations that have not occurred
    return projectionPossiblePredicateCombinations.minus(occurredPredicateCombinations)
  }

  /**
   * Get all [PredicateCombination]s for the given [List] of [TSCInstanceNode]s.
   *
   * @param tscInstances A [List] of [TSCInstanceNode] for which all possible [PredicateCombination]
   * s should be calculated.
   *
   * @return the [Set] of [PredicateCombination]s based on the [tscInstances].
   */
  private fun getAllPredicateCombinations(
      tscInstances: List<TSCInstanceNode<E, T, S>>
  ): Set<PredicateCombination> {
    // Create set for storage of all combinations
    val predicateCombinations = mutableSetOf<PredicateCombination>()
    tscInstances.forEach { t ->
      // Get all TSCEdges that are possible for the current TSCInstance, excluding TSCAlwaysEdges,
      // as they do not
      // represent a predicate
      val allEdgesInValidInstances = t.getAllEdges().filter { it !is TSCAlwaysEdge<E, T, S> }
      // Combine all TSCEdges with each other
      allEdgesInValidInstances.forEach { edge1 ->
        allEdgesInValidInstances
            .filter { it != edge1 }
            .forEach { edge2 ->
              predicateCombinations += PredicateCombination(edge1.label, edge2.label)
            }
      }
    }
    return predicateCombinations
  }
}