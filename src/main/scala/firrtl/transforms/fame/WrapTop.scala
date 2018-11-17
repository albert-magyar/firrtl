// See LICENSE for license details.

package firrtl.transforms.fame

import firrtl._
import ir._
import annotations.CircuitTarget

// Wrap the top module of a circuit with another module
class WrapTop extends Transform {
  def inputForm = HighForm
  def outputForm = HighForm

  override def execute(state: CircuitState): CircuitState = {
    val topName = state.circuit.main
    val topModule = state.circuit.modules.find(_.name == topName).get
    val topInstance = WDefInstance(topName, topName)
    val topWrapperName = Namespace(state.circuit).newName("FAMETop")
    val portConnections = topModule.ports.map({
      case ip @ Port(_, name, Input, _) => Connect(NoInfo, WSubField(WRef(topInstance), name), WRef(ip))
      case op @ Port(_, name, Output, _) => Connect(NoInfo, WRef(op), WSubField(WRef(topInstance), name))
    })
    val topWrapper = Module(NoInfo, topWrapperName, topModule.ports, Block(topInstance +: portConnections))
    val renames = RenameMap()
    val newCircuit = Circuit(state.circuit.info, topWrapper +: state.circuit.modules, topWrapperName)
    renames.record(CircuitTarget(topName), CircuitTarget(topWrapperName))
    state.copy(circuit = newCircuit, renames = Some(renames))
  }
}
