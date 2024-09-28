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

import kotlin.reflect.KClass
import kotlin.time.Duration
import kotlin.time.measureTime
import tools.aqua.stars.data.av.dataclasses.*

fun testReflectionForDataAvPerformance(): Duration {
  val kClasses = mutableListOf<KClass<*>>()
  return measureTime {
    kClasses.add(TickData::class)
    kClasses.add(TrafficLight::class)
    kClasses.add(Block::class)
    kClasses.add(Vehicle::class)
    kClasses.add(Pedestrian::class)
    kClasses.add(Road::class)
    kClasses.add(Lane::class)
    kClasses.add(ContactLaneInfo::class)
    kClasses.add(LaneMidpoint::class)
    kClasses.add(SpeedLimit::class)
    kClasses.add(Landmark::class)
    kClasses.add(ContactArea::class)
    kClasses.add(StaticTrafficLight::class)
    kClasses.add(Location::class)
  }
}

fun main() {
  val times = mutableListOf<Duration>()
  for (i in 0..20) {
    val testRun = testReflectionForDataAvPerformance()
    times.add(testRun)
  }
  println(times)
}
