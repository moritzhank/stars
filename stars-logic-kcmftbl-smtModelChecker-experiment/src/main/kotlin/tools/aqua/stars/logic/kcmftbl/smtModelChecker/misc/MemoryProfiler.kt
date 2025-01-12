package tools.aqua.stars.logic.kcmftbl.smtModelChecker.misc

import oshi.SystemInfo
import oshi.software.os.OSProcess
import kotlin.math.max
import kotlin.math.min

/**
 * Profile the memory used by the system and a particular process.
 */
class MemoryProfiler private constructor(private val pid: Int, val sampleRate: Int = 100) {

  val maxSysMemUsagePercent: Double
  val maxProcMemUsageBytes: Long
  val numSamples: Int
  val elapsedMillis: Long
  val delayMillis: Long

  init {
    var minSysMemAvailable: Long = Long.MAX_VALUE
    var maxProcMemUsageBytes: Long = -1
    var numSamples: Int = 0
    val startMillis = System.currentTimeMillis()
    var sysInfo = SystemInfo()
    val totalMem = sysInfo.hardware.memory.total
    var proc: OSProcess? = sysInfo.operatingSystem.getProcess(pid)
    delayMillis = System.currentTimeMillis() - startMillis
    var t1 = System.currentTimeMillis()
    while(proc != null) {
      if ((System.currentTimeMillis() - t1) < sampleRate) {
        continue
      }
      t1 = System.currentTimeMillis()
      minSysMemAvailable = min(sysInfo.hardware.memory.available, minSysMemAvailable)
      maxProcMemUsageBytes = max(proc.residentSetSize, maxProcMemUsageBytes)
      numSamples++
      try {
        require(proc.updateAttributes())
        sysInfo = SystemInfo()
      } catch (_: Exception) {
        break
      }
    }
    this.maxSysMemUsagePercent = (totalMem - minSysMemAvailable).toDouble() / totalMem
    this.numSamples = numSamples
    this.maxProcMemUsageBytes = maxProcMemUsageBytes
    elapsedMillis = System.currentTimeMillis() - startMillis
  }

  companion object {
    fun start(pid: Int) = MemoryProfiler(pid)
  }
}
