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
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.runCommand
import java.io.File

class DispatcherTCPContext private constructor(private val port: Int, private val containerID: String) {

  private var closed: Boolean = false

  fun close(): Boolean {
    if (closed) {
      return false
    }
    val cmdResult = "docker rm -f $containerID".runCommand(File("/"))
    if (cmdResult != null) {
      closed = true
      return  true
    }
    return false
  }

  suspend fun sendMessage(msg: String): String {
    val selectorManager = SelectorManager(Dispatchers.IO)
    val socket = aSocket(selectorManager).tcp().connect("127.0.0.1", port)
    val writeChannel = socket.openWriteChannel(autoFlush = true)
    val readChannel = socket.openReadChannel()
    writeChannel.writeStringUtf8(msg)
    writeChannel.close()
    val readResult: StringBuilder = StringBuilder("")
    while (true) {
      val line = readChannel.readUTF8Line() ?: break
      readResult.appendLine(line)
    }
    socket.close()
    selectorManager.close()
    return readResult.toString()
  }

  companion object {

    private var currentContext: DispatcherTCPContext? = null

    fun open(): DispatcherTCPContext? {
      if (currentContext == null) {
        val port = 7500
        val cmdResult = "docker run -d --publish $port:7500 smt-solver".runCommand(File("/"))
        if (cmdResult != null) {
          currentContext = DispatcherTCPContext(port, cmdResult.lines()[0])
        }
      }
      return currentContext
    }
  }
}