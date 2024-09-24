import tools.aqua.stars.data.av.dataclasses.Segment
import tools.aqua.stars.importer.carla.CarlaSimulationRunsWrapper
import tools.aqua.stars.importer.carla.loadSegments
import java.nio.file.Paths

class ExperimentLoader {

    companion object {

        fun loadTestSegment() : Segment {
            val dynamic = getPathToResource("dynamic_data__Game_Carla_Maps_Town01_seed2.json")
            val static = getPathToResource("static_data__Game_Carla_Maps_Town01.json")
            val wrapper = CarlaSimulationRunsWrapper(static, listOf(dynamic))
            return loadSegments(listOf(wrapper), false , 10, true).first()
        }

        private fun getPathToResource(name: String) = Paths.get(ExperimentLoader::class.java.getResource(name)!!.toURI())

    }

}