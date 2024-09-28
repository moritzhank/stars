import tools.aqua.stars.data.av.dataclasses.*
import kotlin.reflect.KClass
import kotlin.time.Duration
import kotlin.time.measureTime

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