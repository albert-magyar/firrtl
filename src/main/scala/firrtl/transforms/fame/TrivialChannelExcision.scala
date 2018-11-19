// See LICENSE for license details.

package firrtl.transforms.fame

import firrtl._
import ir._
import Mappers._
import annotations.{ModuleTarget, ReferenceTarget}
import analyses.InstanceGraph
import collection.mutable

/*
 * Trivial Channel Excision
 * This pass does what channel excision would do for the trivial case
 * of one model in low FIRRTL
 */

class TrivialChannelExcision extends Transform {
  def inputForm = LowForm
  def outputForm = LowForm

  override def execute(state: CircuitState): CircuitState = {
    val topName = state.circuit.main
    val topModule = state.circuit.modules.find(_.name == topName).collect({
      case m: Module => m
    }).get
    val topChildren = new mutable.HashSet[WDefInstance]
    topModule.body.map(InstanceGraph.collectInstances(topChildren))
    assert(topChildren.size == 1)
    val fame1Anno = FAMETransformAnnotation(FAME1Transform, ModuleTarget(topName, topChildren.head.module))
    val fameChannelAnnos = topModule.ports.collect({
      case ip @ Port(_, name, Input, tpe) if tpe != ClockType =>
        FAMEChannelAnnotation(s"channel_${name}_sink", WireChannel, None, Some(Seq(ReferenceTarget(topName, topName, Nil, name, Nil))))
      case op @ Port(_, name, Output, tpe) =>
        FAMEChannelAnnotation(s"channel_${name}_source", WireChannel, Some(Seq(ReferenceTarget(topName, topName, Nil, name, Nil))), None)
    })
    state.copy(annotations = state.annotations ++ Seq(fame1Anno) ++ fameChannelAnnos)
  }
}