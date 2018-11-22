// See LICENSE for license details.

package firrtl.transforms.fame

import firrtl._
import ir._
import annotations._

// Label all unbound top-level ports as wire channels
class FAMEDefaults extends Transform {
  def inputForm = HighForm
  def outputForm = HighForm

  override def execute(state: CircuitState): CircuitState = {
    val analysis = new FAMEChannelAnalysis(state, FAME1Transform)
    val topModule = state.circuit.modules.find(_.name == state.circuit.main).get
    val globalSignals = state.annotations.collect({ case g: FAMEGlobalSignal => g.target.ref }).toSet
    def isGlobal(topPort: Port) = globalSignals.contains(topPort.name)
    def isBound(topPort: Port) = analysis.channelsByPort.contains(analysis.topTarget.ref(topPort.name))
    val defaultPortChannels = topModule.ports.filterNot(isGlobal).filterNot(isBound).map({
      case Port(_, name, Input, _) => FAMEChannelAnnotation(name, WireChannel, None, Some(Seq(analysis.topTarget.ref(name))))
      case Port(_, name, Output, _) => FAMEChannelAnnotation(name, WireChannel, Some(Seq(analysis.topTarget.ref(name))), None)
    })
    state.copy(annotations = state.annotations ++ defaultPortChannels)
  }
}
