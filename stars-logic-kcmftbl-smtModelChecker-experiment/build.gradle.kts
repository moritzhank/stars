/*
 * Copyright 2025 The STARS Project Authors
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

val experimentClass = "SmtDistinctPerformanceTestKt"

plugins {
  id("tools.aqua.stars.library-conventions")
  application
}

application {
  mainClass.set("tools.aqua.stars.logic.kcmftbl.smtModelChecker.experiments.$experimentClass")
}

tasks.distZip {
  archiveFileName.set("${experimentClass.dropLast(2)}.zip")
  destinationDirectory.set(rootProject.file("experiment${File.separator}"))
  into("${experimentClass.dropLast(2)}/bin/") {
    from("src/main/resources/")
    include("*/*")
  }
}

dependencies {
  implementation(project(":stars-core"))
  implementation(project(":stars-logic-kcmftbl"))
  implementation(project(":stars-logic-kcmftbl-smtModelChecker"))
  implementation(project(":stars-data-av"))
  implementation(project(":stars-importer-carla"))
  implementation("org.jetbrains.kotlinx:kotlinx-serialization-core:1.7.3")
  implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:1.8.1")
  implementation("com.github.oshi:oshi-core:6.6.5")
}
