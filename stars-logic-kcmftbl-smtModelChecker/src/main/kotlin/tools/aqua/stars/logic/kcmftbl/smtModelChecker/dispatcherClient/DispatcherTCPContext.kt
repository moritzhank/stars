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

package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dispatcherClient

import io.ktor.network.selector.*
import io.ktor.network.sockets.*
import io.ktor.utils.io.*
import kotlinx.coroutines.Dispatchers

class DispatcherTCPContext(private val ipAdress: String, private val port: Int) {

  suspend fun sendMessage(msg: String): String {
    val selectorManager = SelectorManager(Dispatchers.IO)
    val socket = aSocket(selectorManager).tcp().connect(ipAdress, port)
    val writeChannel = socket.openWriteChannel(autoFlush = true)
    val readChannel = socket.openReadChannel()
    writeChannel.writeStringUtf8(msg)

    val lines = msg.lines()
    lines.forEachIndexed { index, line ->
      println(index)
      writeChannel.writeStringUtf8("$line\n")
    }
    writeChannel.writeStringUtf8("\$EOF\$\n")
    val readResult: StringBuilder = StringBuilder("")
    while (true) {
      val line = readChannel.readUTF8Line() ?: break
      readResult.appendLine(line)
    }
    socket.close()
    selectorManager.close()
    return readResult.toString()
  }
}
