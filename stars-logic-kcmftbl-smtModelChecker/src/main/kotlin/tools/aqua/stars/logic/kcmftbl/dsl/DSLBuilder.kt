package tools.aqua.stars.logic.kcmftbl.dsl

sealed interface DSLBuilder {

  val allowedCCBs: List<CCB<*>>

  fun isAllowedCC(cc: CallContext<*, *>) = allowedCCBs.contains(cc.base)
}