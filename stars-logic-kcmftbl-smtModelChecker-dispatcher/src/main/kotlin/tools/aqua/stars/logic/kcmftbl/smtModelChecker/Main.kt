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

import io.ktor.network.selector.*
import io.ktor.network.sockets.*
import io.ktor.utils.io.*
import java.io.File
import java.util.*
import java.util.concurrent.Executors
import kotlinx.coroutines.asCoroutineDispatcher
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking

const val PORT = 7500
const val MAX_LINES = 10_000
const val EOF_STRING = "\$EOF\$"
const val jobsDir = "/root/jobs"

fun main() {
  File(jobsDir).mkdir()
  runBlocking {
    val selectorManager =
        ActorSelectorManager(Executors.newCachedThreadPool().asCoroutineDispatcher())
    val server = aSocket(selectorManager).tcp().bind(InetSocketAddress("0.0.0.0", PORT))
    log("Listening now on 0.0.0.0:$PORT ...")
    while (true) {
      val socket = server.accept()
      log("Accepted ${socket.remoteAddress}")
      val receiveChannel = socket.openReadChannel()
      val sendChannel = socket.openWriteChannel(autoFlush = false)
      launch {
        try {
          val solver =
              receiveChannel.readUTF8Line()?.lowercase() ?: throw IllegalArgumentException()
          if (solver != "z3" && solver != "cvc5") {
            throw DispatcherFormatException(
                "The initial line of the request must be the name of the solver.")
          }
          sendChannel.writeStringUtf8("Solver was set to $solver.\n")
          val lines = StringBuilder()
          var lineCount = 0
          var readEndOfFileString = false
          while (!readEndOfFileString && lineCount < MAX_LINES) {
            val line = receiveChannel.readUTF8Line() ?: throw IllegalArgumentException()
            if (line == EOF_STRING) {
              readEndOfFileString = true
              continue
            }
            lines.appendLine(line)
            lineCount++
          }
          sendChannel.writeStringUtf8("Received $lineCount line(s).\nStarting solver ...\n")
          runSmtSolver(solver, lines.toString(), sendChannel)
        } catch (e: DispatcherFormatException) {
          sendChannel.writeStringUtf8("Error: ${e.message!!}")
        } catch (e: Exception) {
          log(e.stackTraceToString())
        } finally {
          val remoteAddr = socket.remoteAddress
          socket.close()
          log("Closed $remoteAddr")
        }
      }
    }
  }
}

fun log(content: String) {
  println("[SMT-DISPATCHER] $content")
}

private suspend fun runSmtSolver(solver: String, lines: String, sendChannel: ByteWriteChannel) {
  // Generate file
  val fileName = "$jobsDir/${UUID.randomUUID()}.smt2"
  val file = File(fileName)
  file.writeText(lines)
  // Run solver
  val result =
      if (solver == "cvc5") {
        "./cvc5 $fileName".runCommand()
      } else {
        "z3 $fileName".runCommand()
      }
  // Error handling
  if (result != null) {
    sendChannel.writeStringUtf8(result.output)
    if (result.exitCode != 0 && result.error.isNotEmpty()) {
      sendChannel.writeStringUtf8(result.error)
    }
  }
  file.delete()
}
