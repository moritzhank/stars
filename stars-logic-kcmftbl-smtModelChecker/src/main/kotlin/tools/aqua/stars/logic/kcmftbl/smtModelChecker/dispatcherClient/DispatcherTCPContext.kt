package tools.aqua.stars.logic.kcmftbl.smtModelChecker.dispatcherClient

import tools.aqua.stars.logic.kcmftbl.dsl.CallContext
import tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc.runCommand
import java.io.File

class DispatcherTCPContext private constructor(private val port: Int) {

  companion object {

    private var currentContext: DispatcherTCPContext? = null

    fun open(): DispatcherTCPContext? {
      if(currentContext == null) {
        val port = 7500
        val cmdResult = "docker run --publish $port:7500 smt-solver".runCommand(File("/"))
        if(cmdResult != null) {
          currentContext = DispatcherTCPContext(port)
        }
      }
      return currentContext
    }

  }


}