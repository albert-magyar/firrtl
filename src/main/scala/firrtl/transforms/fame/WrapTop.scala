// See LICENSE for license details.

package firrtl.transforms.fame

import firrtl._
import ir._
import annotations._

// Wrap the top module of a circuit with another module
class WrapTop extends Transform {
  def inputForm = HighForm
  def outputForm = HighForm

  override def execute(state: CircuitState): CircuitState = {
    val topName = state.circuit.main
    val topModule = state.circuit.modules.find(_.name == topName).get
    val circuitNS = Namespace(state.circuit)
    val topWrapperName = circuitNS.newName("FAMETop")
    val topWrapperNS = Namespace(topModule.ports.map(_.name))
    val topInstance = WDefInstance(topWrapperNS.newName(topName), topName)
    val portConnections = topModule.ports.map({
      case ip @ Port(_, name, Input, _) => Connect(NoInfo, WSubField(WRef(topInstance), name), WRef(ip))
      case op @ Port(_, name, Output, _) => Connect(NoInfo, WRef(op), WSubField(WRef(topInstance), name))
    })
    val clocks = topModule.ports.filter(_.tpe == ClockType)
    val hostClock = clocks.find(_.name == "clock").getOrElse(clocks.head)
    val hostReset = HostReset.makePort(topWrapperNS)
    val topWrapperTarget = ModuleTarget(topWrapperName, topWrapperName)
    val topWrapper = Module(NoInfo, topWrapperName, topModule.ports :+ hostReset, Block(topInstance +: portConnections))
    val specialPortAnnotations = Seq(FAMEHostClock(topWrapperTarget.ref(hostClock.name)), FAMEHostReset(topWrapperTarget.ref(hostReset.name)))
    val renames = RenameMap()
    val newCircuit = Circuit(state.circuit.info, topWrapper +: state.circuit.modules, topWrapperName)
    renames.record(CircuitTarget(topName), topWrapperTarget.targetParent)
    state.copy(circuit = newCircuit, annotations = state.annotations ++ specialPortAnnotations, renames = Some(renames))
  }
}
