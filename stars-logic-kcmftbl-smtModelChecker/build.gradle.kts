/*
 * Copyright 2022-2024 The STARS Project Authors
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

plugins {
  id("tools.aqua.stars.library-conventions")
  kotlin("plugin.serialization") version "2.0.20"
}

dependencies {
  implementation(kotlin("reflect"))
  implementation(project(":stars-core"))
  implementation(project(":stars-logic-kcmftbl"))
  implementation("org.jetbrains.kotlinx:kotlinx-metadata-jvm:0.9.0")
  implementation("org.jetbrains.kotlinx:kotlinx-serialization-core:1.7.3")
  implementation("io.ktor:ktor-network:2.3.12")
  testImplementation(project(mapOf("path" to ":stars-data-av")))
  testImplementation(project(":stars-data-av", "test"))
}

tasks.build { dependsOn("buildDockerImage") }

tasks.processResources { dependsOn("copyShadowJar") }

task<Exec>("buildDockerImage") {
  dependsOn(tasks.processResources)
  setWorkingDir("build/resources/main/")
  commandLine("docker", "build", ".", "-t", "smt-solver")
}

task<Copy>("copyShadowJar") {
  dependsOn(":stars-logic-kcmftbl-smtModelChecker-dispatcher:shadowJar")
  from(project(":stars-logic-kcmftbl-smtModelChecker-dispatcher").file("build/libs/dispatcher.jar"))
  into("build/resources/main/")
}
