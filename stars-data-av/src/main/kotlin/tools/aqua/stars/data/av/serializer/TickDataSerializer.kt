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

package tools.aqua.stars.data.av.serializer

import kotlinx.serialization.KSerializer
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.descriptors.element
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.encoding.encodeStructure
import tools.aqua.stars.data.av.dataclasses.Block
import tools.aqua.stars.data.av.dataclasses.Daytime
import tools.aqua.stars.data.av.dataclasses.Pedestrian
import tools.aqua.stars.data.av.dataclasses.Segment
import tools.aqua.stars.data.av.dataclasses.TickData
import tools.aqua.stars.data.av.dataclasses.TickDataUnitSeconds
import tools.aqua.stars.data.av.dataclasses.TrafficLight
import tools.aqua.stars.data.av.dataclasses.Vehicle
import tools.aqua.stars.data.av.dataclasses.WeatherParameters

class TickDataSerializer() : KSerializer<TickData> {

  override val descriptor: SerialDescriptor =
      buildClassSerialDescriptor("TickData") {
        element<TickDataUnitSeconds>("currentTick")
        element<List<TrafficLight>>("trafficLights")
        element<List<Block>>("blocks")
        element<WeatherParameters>("weather")
        element<Daytime>("daytime")
        element<Segment>("segment")
        element<List<Vehicle>>("vehicles")
        element<List<Pedestrian>>("pedestrians")
      }

  override fun serialize(encoder: Encoder, value: TickData) {
    encoder.encodeStructure(descriptor) {
      encodeSerializableElement(descriptor, 0, TickDataUnitSeconds.serializer(), value.currentTick)
      encodeSerializableElement(
          descriptor, 1, ListSerializer(TrafficLight.serializer()), value.trafficLights)
      encodeSerializableElement(descriptor, 2, ListSerializer(Block.serializer()), value.blocks)
      encodeSerializableElement(descriptor, 3, WeatherParameters.serializer(), value.weather)
      encodeSerializableElement(descriptor, 4, Daytime.serializer(), value.daytime)
      encodeSerializableElement(descriptor, 5, Segment.serializer(), value.segment)
      encodeSerializableElement(descriptor, 6, ListSerializer(Vehicle.serializer()), value.vehicles)
      encodeSerializableElement(
          descriptor, 7, ListSerializer(Pedestrian.serializer()), value.pedestrians)
    }
  }

  override fun deserialize(decoder: Decoder): TickData {
    error("This serializer does not support decoding.")
  }
}
