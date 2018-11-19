// See LICENSE for license details.

package firrtl.transforms.fame

import java.io.{PrintWriter, File}

import firrtl._
import ir._
import Mappers._
import Utils._
import passes.MemPortUtils
import annotations.{ModuleTarget, InstanceTarget, Annotation, SingleTargetAnnotation}
import scala.collection.mutable
import mutable.{LinkedHashSet, LinkedHashMap}

/**************
 PRECONDITIONS:
 **************
 1.) Ports do not have aggregate types (easy to support if necessary)
 2.) There are no collisions among input/output channel names
 */

trait FAME1Channel {
  def name: String
  def direction: Direction
  def ports: Seq[Port]
  def tpe: Type = FAMEChannelAnalysis.getChannelType(name, ports)
  def asPort: Port = Port(NoInfo, name, direction, tpe)
  def isReady: Expression = WSubField(WRef(asPort), "ready", Utils.BoolType)
  def isValid: Expression = WSubField(WRef(asPort), "valid", Utils.BoolType)
  def isFiring: Expression = Reduce.and(Seq(isReady, isValid))
  def replacePortRef(wr: WRef): WSubField = {
    if (ports.size > 1) {
      WSubField(WSubField(WRef(asPort), "bits"), FAMEChannelAnalysis.removeCommonPrefix(wr.name, name)._1)
    } else {
      WSubField(WRef(asPort), "bits")
    }
  }
}

case class FAME1InputChannel(val name: String, val ports: Seq[Port]) extends FAME1Channel {
  val direction = Input
  def genTokenLogic(finishing: WRef): Seq[Statement] = {
    Seq(Connect(NoInfo, isReady, finishing))
  }
}

case class FAME1OutputChannel(val name: String, val ports: Seq[Port], val firedReg: DefRegister) extends FAME1Channel {
  val direction = Output
  val isFired = WRef(firedReg)
  val isFiredOrFiring = Reduce.or(Seq(isFired, isFiring))
  def genTokenLogic(finishing: WRef, ccDeps: Iterable[FAME1InputChannel]): Seq[Statement] = {
    val regUpdate = Connect(
      NoInfo,
      isFired,
      Mux(finishing,
        UIntLiteral(0, IntWidth(1)),
        isFiredOrFiring,
        Utils.BoolType))
    val setValid = Connect(
      NoInfo,
      isValid,
      Reduce.and(ccDeps.map(_.isValid) ++ Seq(Negate(isFired))))
    Seq(regUpdate, setValid)
  }
}

object ChannelCCDependencyGraph {
  def apply(m: Module): LinkedHashMap[FAME1OutputChannel, LinkedHashSet[FAME1InputChannel]] = {
    new LinkedHashMap[FAME1OutputChannel, LinkedHashSet[FAME1InputChannel]]
  }
}

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
  def apply(m: Module, analysis: FAMEChannelAnalysis)(implicit triggerName: String): Module = {
    val ns = Namespace(m)
    val clocks = m.ports.filter(_.tpe == ClockType)
    // TODO: turn this back on
    // assert(clocks.length == 1)
    val finishing = new Port(NoInfo, ns.newName(triggerName), Input, Utils.BoolType)
    val hostClock = clocks.find(_.name == "clock").getOrElse(clocks.head) // TODO: naming convention for host clock
    def onStmt(stmt: Statement): Statement = stmt.map(onStmt) match {
      case conn @ Connect(info, lhs, _) if (kind(lhs) == RegKind) =>
        Conditionally(info, WRef(finishing), conn, EmptyStmt)
      case s: Stop  => s.copy(en = DoPrim(PrimOps.And, Seq(WRef(finishing), s.en), Seq.empty, BoolType))
      case p: Print => p.copy(en = DoPrim(PrimOps.And, Seq(WRef(finishing), p.en), Seq.empty, BoolType))
      case mem: DefMemory => PatientMemTransformer(mem, WRef(finishing), WRef(hostClock), ns)
      case wi: WDefInstance if analysis.syncModules.contains(ModuleTarget(analysis.circuit.main, wi.module)) =>
        new Block(Seq(wi, Connect(wi.info, WSubField(WRef(wi), triggerName), WRef(finishing))))
      case s => s
    }
    Module(m.info, m.name, m.ports :+ finishing, m.body.map(onStmt))
  }
}

object FAMEModuleTransformer {
  def apply(m: Module, analysis: FAMEChannelAnalysis)(implicit triggerName: String): Module = {
    // Step 0: Special signals & bookkeeping
    val ns = Namespace(m)
    val clocks = m.ports.filter(_.tpe == ClockType)
    // TODO: turn this back to == 1
    assert(clocks.length >= 1)
    val hostClock = clocks.find(_.name == "clock").getOrElse(clocks.head) // TODO: naming convention for host clock
    val hostReset = HostReset.makePort(ns)
    def createHostReg(name: String = "host", width: Width = IntWidth(1)): DefRegister = {
      new DefRegister(NoInfo, ns.newName(name), UIntType(width), WRef(hostClock), WRef(hostReset), UIntLiteral(0, width))
    }
    val finishing = DefWire(NoInfo, ns.newName(triggerName), Utils.BoolType)

    // Step 1: Build channels
    val inChannels = analysis.inputPortsByChannel(m).map({
      case (cName, ports) => new FAME1InputChannel(cName, ports)
    })
    val inChannelMap = new LinkedHashMap[String, FAME1InputChannel] ++
      (inChannels.flatMap(c => c.ports.map(p => (p.name, c))))
    val outChannels = analysis.outputPortsByChannel(m).map({
      case (cName, ports) =>
        val firedReg = createHostReg(name = ns.newName(s"${cName}_fired"))
        new FAME1OutputChannel(cName, ports, firedReg)
    })
    val outChannelMap = new LinkedHashMap[String, FAME1OutputChannel] ++
      (outChannels.flatMap(c => c.ports.map(p => (p.name, c))))
    val decls = Seq(finishing) ++ outChannels.map(_.firedReg)


    // Step 2: Find combinational dependencies
    val ccChecker = new transforms.CheckCombLoops
    val portDeps = ccChecker.analyzeModule(analysis.circuit, m)
    val ccDeps = new LinkedHashMap[FAME1OutputChannel, LinkedHashSet[FAME1InputChannel]]
    portDeps.getEdgeMap.collect({ case (o, iSet) if outChannelMap.contains(o) =>
      ccDeps.getOrElseUpdate(outChannelMap(o), new LinkedHashSet[FAME1InputChannel])
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
      case wi: WDefInstance if analysis.syncModules.contains(analysis.topTarget.copy(module = wi.module)) =>
        new Block(Seq(wi, Connect(wi.info, WSubField(WRef(wi), triggerName), WRef(finishing))))
      case s: Stop  => s.copy(en = DoPrim(PrimOps.And, Seq(WRef(finishing), s.en), Seq.empty, BoolType))
      case p: Print => p.copy(en = DoPrim(PrimOps.And, Seq(WRef(finishing), p.en), Seq.empty, BoolType))
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

  def deleteStaleConnects(analysis: FAMEChannelAnalysis)(stmt: Statement): Statement = stmt.map(deleteStaleConnects(analysis)) match {
    case Connect(_, WRef(name, _, _, _), _) if (analysis.staleTopPorts.contains(analysis.topTarget.ref(name))) => EmptyStmt
    case Connect(_, _, WRef(name, _, _, _)) if (analysis.staleTopPorts.contains(analysis.topTarget.ref(name))) => EmptyStmt
    case s => s
  }

  def transformTop(top: DefModule, analysis: FAMEChannelAnalysis): Module = top match {
    case Module(info, name, ports, body) =>
      val transformedPorts = ports.filterNot(p => analysis.staleTopPorts.contains(analysis.topTarget.ref(p.name))) ++
        analysis.transformedSinks.map(c => Port(NoInfo, c, Input, analysis.getSinkChannelType(c))) ++
        analysis.transformedSources.map(c => Port(NoInfo, c, Output, analysis.getSourceChannelType(c)))
      val transformedStmts = Seq(body.map(deleteStaleConnects(analysis))) ++
        analysis.transformedSinks.map({c => Connect(NoInfo, WSubField(WRef(analysis.sinkModel(c).module), c), WRef(c))}) ++
        analysis.transformedSources.map({c => Connect(NoInfo, WRef(c), WSubField(WRef(analysis.sourceModel(c).module), c))}) ++
        analysis.transformedModules.map({m => Connect(NoInfo, WSubField(WRef(m.module), "hostReset"),
          WRef(top.ports.find(_.name == "hostReset").get))})
      Module(info, name, transformedPorts, Block(transformedStmts))
  }

  override def execute(state: CircuitState): CircuitState = {
    val c = state.circuit
    val analysis = new FAMEChannelAnalysis(state, FAME1Transform)
    // TODO: pick a value that does not collide
    implicit val triggerName = "finishing"
    val transformedModules = c.modules.map {
      case m: Module if (m.name == c.main) => transformTop(m, analysis)
      case m: Module if (analysis.transformedModules.contains(ModuleTarget(c.main,m.name))) => FAMEModuleTransformer(m, analysis)
      case m: Module if (analysis.syncModules.contains(ModuleTarget(c.main, m.name))) => PatientSSMTransformer(m, analysis)
      case m => m
    }
    state.copy(circuit = c.copy(modules = transformedModules))
  }
}
