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

import kotlinx.metadata.isNotDefault
import kotlinx.metadata.jvm.KotlinClassMetadata
import java.io.File
import java.util.concurrent.TimeUnit
import kotlin.reflect.KProperty1

// Copied and modified from https://stackoverflow.com/a/41495542
fun String.runCommand(workingDir: File, timeOutInMS: Long = 60 * 60 * 1000): String? {
  try {
    val parts = this.split("\\s".toRegex())
    val proc =
        ProcessBuilder(*parts.toTypedArray())
            .directory(workingDir)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start()
    proc.waitFor(timeOutInMS, TimeUnit.MILLISECONDS)
    if (proc.exitValue() != 0)
        throw IllegalStateException(
            "Error executing a command:${System.lineSeparator()}${proc.errorStream.bufferedReader().readText()}")
    return proc.inputStream.bufferedReader().readText()
  } catch (e: Exception) {
    e.printStackTrace()
    return null
  }
}

// Adapted from https://discuss.kotlinlang.org/t/reflection-and-properties-checking-for-custom-getters-setters/22457/2
/** Returns false if the property does not have a default getter, or if it cannot be determined */
inline fun <reified Receiver, reified Property> KProperty1<Receiver, Property>.hasDefaultGetter():
    Boolean {
  val meta = Receiver::class.java.getAnnotation(Metadata::class.java) ?: return false
  val metadataAnnotation =
    Metadata(
      kind = meta.kind,
      metadataVersion = meta.metadataVersion,
      data1 = meta.data1,
      data2 = meta.data2,
      extraString = meta.extraString,
      packageName = meta.packageName,
      extraInt = meta.extraInt)
  return !((KotlinClassMetadata.readStrict(metadataAnnotation) as KotlinClassMetadata.Class)
    .kmClass
    .properties
    .find { it.name == this.name }
    ?.getter
    ?.isNotDefault ?: true)
}
