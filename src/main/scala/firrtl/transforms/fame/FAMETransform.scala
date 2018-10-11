// See LICENSE for license details.

package firrtl.transforms.fame

import firrtl._
import ir._
import Mappers._
import Utils._
import passes.MemPortUtils
import annotations._
import scala.collection.mutable
import mutable.{LinkedHashSet, LinkedHashMap}

/**************
 PRECONDITIONS:
 **************
 1.) Ports do not have aggregate types (easy to support if necessary)
 2.) There are no collisions among input/output channel names
 */

object PatientMemTransformer {
  def apply(mem: DefMemory, finishing: WRef, memClock: WRef, ns: Namespace): Block = {
    val shim = DefWire(NoInfo, mem.name, MemPortUtils.memType(mem))
    val newMem = mem.copy(name = ns.newName(mem.name))
    val defaultConnect = Connect(NoInfo, WRef(shim), WRef(newMem.name, shim.tpe, MemKind))
    val syncReadPorts = (newMem.readers ++ newMem.readwriters).filter(rp => mem.readLatency > 0)
    val preserveReads = syncReadPorts.flatMap {
      case rpName =>
        val addrWidth = IntWidth(ceilLog2(mem.depth) max 1)
        val addrReg = new DefRegister(NoInfo, ns.newName(s"${mem.name}_${rpName}"),
          UIntType(addrWidth), memClock, UIntLiteral(0), UIntLiteral(0, addrWidth))
        val updateReg = Connect(NoInfo, WRef(addrReg), WSubField(WSubField(WRef(shim), rpName), "addr"))
        val useReg = Connect(NoInfo, MemPortUtils.memPortField(newMem, rpName, "addr"), WRef(addrReg))
        Seq(addrReg, Conditionally(NoInfo, finishing, updateReg, useReg))
    }
    val gateWrites = (newMem.writers ++ newMem.readwriters).map {
      case wpName =>
        Conditionally(
          NoInfo,
          Negate(finishing),
          Connect(NoInfo, MemPortUtils.memPortField(newMem, wpName, "en"), UIntLiteral(0, IntWidth(1))),
          EmptyStmt)
      }
    new Block(Seq(shim, newMem, defaultConnect) ++ preserveReads ++ gateWrites)
  }
}

object PatientSSMTransformer {
  def apply(m: Module)(implicit triggerName: String): Module = {
    val ns = Namespace(m)
    val clocks = m.ports.filter(_.tpe == ClockType)
    assert(clocks.length == 1)
    val finishing = new Port(NoInfo, ns.newName(triggerName), Input, Utils.BoolType)
    val hostClock = clocks.head // TODO: naming convention for host clock
    def onStmt(stmt: Statement): Statement = stmt.map(onStmt) match {
      case conn @ Connect(info, lhs, _) if (kind(lhs) == RegKind) =>
        Conditionally(info, WRef(finishing), conn, EmptyStmt)
      case mem: DefMemory => PatientMemTransformer(mem, WRef(finishing), WRef(hostClock), ns)
      case wi: WDefInstance => new Block(Seq(wi, Connect(wi.info, WSubField(WRef(wi), triggerName), WRef(finishing))))
      case s => s
    }
    Module(m.info, m.name, m.ports :+ finishing, m.body.map(onStmt))
  }
}

object FAMEModuleTransformer {
  def apply(c: Circuit, m: Module, ann: FAMETransformAnnotation)(implicit triggerName: String): Module = {
    // Step 0: Special signals & bookkeeping
    val ns = Namespace(m)
    val portMap = ann.bindToModule(m)
    val clocks = m.ports.filter(_.tpe == ClockType)
    assert(clocks.length == 1)
    val hostClock = clocks.head // TODO: naming convention for host clock
    val hostReset = new Port(NoInfo, ns.newName("hostReset"), Input, Utils.BoolType)
    def createHostReg(name: String = "host", width: Width = IntWidth(1)): DefRegister = {
      new DefRegister(NoInfo, ns.newName(name), UIntType(width), WRef(hostClock), WRef(hostReset), UIntLiteral(0, width))
    }
    val finishing = DefWire(NoInfo, ns.newName(triggerName), Utils.BoolType)

    // Step 1: Build channels
    val inChannels = portMap.getInputChannels(m).map {
      case (cName, pSet) => new InputChannel(cName, pSet)
    }
    val inChannelMap = new LinkedHashMap[String, InputChannel] ++
      (inChannels.flatMap(c => c.ports.map(p => (p.name, c))))
    val outChannels = portMap.getOutputChannels(m).map {
      case (cName, pSet) =>
        val firedReg = createHostReg(name = ns.newName(s"${cName}_fired"))
        new OutputChannel(cName, pSet, firedReg)
    }
    val outChannelMap = new LinkedHashMap[String, OutputChannel] ++
      (outChannels.flatMap(c => c.ports.map(p => (p.name, c))))
    val decls = Seq(finishing) ++ outChannels.map(_.firedReg)


    // Step 2: Find combinational dependencies
    val ccChecker = new transforms.CheckCombLoops
    val portDeps = ccChecker.analyzeModule(c, m)
    val ccDeps = new LinkedHashMap[OutputChannel, LinkedHashSet[InputChannel]]
    portDeps.getEdgeMap.collect({ case (o, iSet) if outChannelMap.contains(o) =>
      ccDeps.getOrElseUpdate(outChannelMap(o), new LinkedHashSet[InputChannel])
      iSet.foreach(i => ccDeps(outChannelMap(o)) += inChannelMap(i) )})

    // Step 3: transform ports
    val transformedPorts = clocks ++ Seq(hostReset) ++ inChannels.map(_.asPort) ++ outChannels.map(_.asPort)

    // Step 4: Replace refs and gate state updates
    def onExpr(expr: Expression): Expression = expr.map(onExpr) match {
      case iWR @ WRef(name, tpe, PortKind, MALE) if tpe != ClockType =>
        // Generally MALE references to ports will be input channels, but RTL may use
        // an assignment to an output port as something akin to a wire, so check output ports too.
        inChannelMap.getOrElse(name, outChannelMap(name)).replacePortRef(iWR)
      case oWR @ WRef(name, tpe, PortKind, FEMALE) if tpe != ClockType =>
        outChannelMap(name).replacePortRef(oWR)
      case e => e
    }

    def onStmt(stmt: Statement): Statement = stmt.map(onStmt).map(onExpr) match {
      case conn @ Connect(info, lhs, _) if (kind(lhs) == RegKind) =>
        Conditionally(info, WRef(finishing), conn, EmptyStmt)
      case mem: DefMemory => PatientMemTransformer(mem, WRef(finishing), WRef(hostClock), ns)
      case wi: WDefInstance => new Block(Seq(wi, Connect(wi.info, WSubField(WRef(wi), triggerName), WRef(finishing))))
      case s => s
    }

    val transformedStmts = Seq(m.body.map(onStmt))

    // Step 5: Add firing rules for output channels, trigger end of cycle
    val ruleStmts = new mutable.ArrayBuffer[Statement]
    ruleStmts ++= outChannels.flatMap(o => o.genTokenLogic(WRef(finishing), ccDeps(o)))
    ruleStmts ++= inChannels.flatMap(i => i.genTokenLogic(WRef(finishing)))
    ruleStmts += Connect(NoInfo, WRef(finishing),
      Reduce.and(outChannels.map(_.isFiredOrFiring) ++ inChannels.map(_.isValid)))

    Module(m.info, m.name, transformedPorts, new Block(decls ++ transformedStmts ++ ruleStmts))
  }
}

class FAMETransform extends Transform {
  def inputForm = LowForm
  def outputForm = HighForm

  override def execute(state: CircuitState): CircuitState = {
    val c = state.circuit
    val anns = state.annotations.collect {
      case a @ FAMETransformAnnotation(ModuleName(name, _), _) => (name, a)
    }
    implicit val triggerName = "finishing" // TODO: pick a value that does not collide
    val annMap = anns.toMap
    val transformedModules = c.modules.map {
      case m @ Module(_, c.main, _, _) => if (annMap.contains(m.name)) FAMEModuleTransformer(c, m, annMap(m.name)) else FAMEModuleTransformer(c, m, FAMEAnnotate(c, m))
      case m: Module => PatientSSMTransformer(m)
      case m => m
    }
    state.copy(circuit = c.copy(modules = transformedModules))
  }
}
