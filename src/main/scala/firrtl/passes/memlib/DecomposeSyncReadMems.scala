// See LICENSE for license details.

package firrtl
package passes
package memlib

import firrtl.ir._
import firrtl.Mappers._
import firrtl.annotations._
import firrtl.passes._
import firrtl.passes.memlib._
import scala.collection.mutable

import Utils._
import AnalysisUtils._
import MemPortUtils._
import ResolveMaskGranularity._

/**
  * Convert sync-read mems to comb. read mems with pipelined outputs when legal.
  */
object DecomposeSyncReadMems extends Transform {
  def inputForm = MidForm
  def outputForm = MidForm

  def isCandidateMem(m: DefMemory): Boolean = {
    m.type.isInstanceOf[GroundType] && m.readLatency == 1 && m.writeLatency == 1 && m.readUnderWrite.forall(_ == "old")
  }

  def onModule(m: DefModule): DefModule = {
    val moduleNS = Namespace(m)
    // Maps (memName, readPortName) tuples to their associated data pipes
    val dataPipes = new mutable.LinkedHashMap[(String, String), DefRegister]

    def onExpr(e: Expression): Expression = e match {
      case rDataRef @ WSubField(cExp, "data", _, _) => WSubField(WRef(memName, _, MemKind, _), portName, _, _) =>
        dataPipes.getOrElse((memName, portName), portRef)
      case e => e map onExpr
    }

    def addDataPipes(m: DefMemory) = 

    def onStmt(s: Statement): Statement = s match {
      case m: DefMemory if isCandidateMem(m) =>
        val rPipes = m.readers.map
        m.
    def onExpr(e: Expression): Expression = e.map(onExpr) match {
      case WRef(name, tpe, MemKind, gender) if memAdapters.contains(name) =>
        WRef(name, tpe, WireKind, gender)
      case e => e
    }

    def simplifyMem(mem: DefMemory): Statement = {
      val adapterDecl = DefWire(mem.info, mem.name, memType(mem))
      val simpleMemDecl = mem.copy(name = moduleNS.newName(s"${mem.name}_flattened"), dataType = flattenType(mem.dataType))
      val oldRT = mTarget.ref(mem.name)
      val adapterConnects = memType(simpleMemDecl).fields.flatMap {
        case Field(pName, Flip, pType: BundleType) =>
          val memPort = WSubField(WRef(simpleMemDecl), pName)
          val adapterPort = WSubField(WRef(adapterDecl), pName)
          renames.delete(oldRT.field(pName))
          pType.fields.map {
            case Field(name, Flip, _) if name.contains("data") => // read data
              fromBits(WSubField(adapterPort, name), WSubField(memPort, name))
            case Field(name, Default, _) if name.contains("data") => // write data
              Connect(mem.info, WSubField(memPort, name), toBits(WSubField(adapterPort, name)))
            case Field(name, Default, _) if name.contains("mask") => // mask
              Connect(mem.info, WSubField(memPort, name), Utils.one)
            case Field(name, _, _) => // etc
              Connect(mem.info, WSubField(memPort, name), WSubField(adapterPort, name))
          }
      }
      memAdapters(mem.name) = adapterDecl 
      renames.record(oldRT, oldRT.copy(ref = simpleMemDecl.name))
      Block(Seq(adapterDecl, simpleMemDecl) ++ adapterConnects)
    }
  
    def canSimplify(mem: DefMemory) = mem.dataType match {
      case at: AggregateType =>
        val wMasks = mem.writers.map(w => getMaskBits(connects, memPortField(mem, w, "en"), memPortField(mem, w, "mask")))
        val rwMasks = mem.readwriters.map(w => getMaskBits(connects, memPortField(mem, w, "wmode"), memPortField(mem, w, "wmask")))
        (wMasks ++ rwMasks).flatten.isEmpty
      case _ => false
    }

    def onStmt(s: Statement): Statement = s match {
      case mem: DefMemory if canSimplify(mem) => simplifyMem(mem)
      case s => s.map(onStmt).map(onExpr)
    }

    m.map(onStmt)
  }

  override def execute(state: CircuitState): CircuitState = {
    val c = state.circuit
    val renames = RenameMap()
    CircuitState(c.map(onModule(c, renames)(_)), outputForm, state.annotations, Some(renames))
  }
}
