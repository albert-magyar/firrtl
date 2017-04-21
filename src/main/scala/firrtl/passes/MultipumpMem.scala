// See LICENSE for license details.

package firrtl
package passes

import scala.collection.immutable
import scala.collection.mutable

import firrtl.ir._
import firrtl.PrimOps._
import firrtl.Mappers._

object ModuleBundleType {
  // TODO: check if this should be reversed
  private def dirToFlip(d: Direction) = d match {
    case Input => Default
    case Output => Flip
  }

  def apply(m: DefModule): Type = {
    BundleType(m.ports.map(p => Field(p.name,dirToFlip(p.direction),p.tpe)))
  }
}

abstract class MemPort {
  val name: String
}
case class ReadPort(name: String) extends MemPort
case class WritePort(name: String) extends MemPort
case class ReadWritePort(name: String) extends MemPort

object MemType {
  private def log2Ceil(n: Int): Int = {
    require(n > 0)
      BigInt(n-1).bitLength
  }

  private def addrType(depth: Int) = UIntType(IntWidth(log2Ceil(depth)))

  def cmdType(p: MemPort, m: DefMemory) = p match {
    case rp: ReadPort =>
      BundleType(Seq(
        Field("addr",Default,addrType(m.depth)),
        Field("en",Default,UIntType(IntWidth(1)))))
    case wp: WritePort =>
      BundleType(Seq(
        Field("addr",Default,addrType(m.depth)),
        Field("data",Default,m.dataType),
        Field("mask",Default,createMask(m.dataType)),
        Field("en",Default,UIntType(IntWidth(1)))))
    case wp: ReadWritePort =>
      BundleType(Seq(
        Field("addr",Default,addrType(m.depth)),
        Field("wdata",Default,m.dataType),
        Field("wmask",Default,createMask(m.dataType)),
        Field("wmode",Default,UIntType(IntWidth(1))),
        Field("en",Default,UIntType(IntWidth(1)))))
  }

  def portType(p: MemPort, m: DefMemory) = {
    val cmdResp = p match {
      case rp: ReadPort =>
        val rCmdType = cmdType(p,m)
        rCmdType.copy(fields = rCmdType.fields :+ Field("data",Flip,m.dataType))
      case wp: WritePort =>
        cmdType(p,m)
      case rwp: ReadWritePort =>
        val rCmdType = cmdType(p,m)
        rCmdType.copy(fields = rCmdType.fields :+ Field("rdata",Flip,m.dataType))
    }
    cmdResp.copy(fields = cmdResp.fields :+ Field("clk",Default,ClockType))
  }

  def apply(m: DefMemory): Type = {
    val memPorts = m.readers.map(ReadPort(_)) ++
      m.writers.map(WritePort(_)) ++
      m.readwriters.map(ReadWritePort(_))
    val memFields = memPorts.map(p => Field(p.name,Default,portType(p,m)))
    BundleType(memFields)
  }
}

object MultipumpMem extends Pass {

  // TODO: get fresh name
  private def getName(desired: String): String = {
    desired
  }

  private case class ClockDoublerInstance(
    statements: Seq[Statement],
    slowClock: Expression,
    fastClock: Expression)

  private abstract class ClockDoubler {
    val defn: DefModule
    def double(slowClock: Expression): ClockDoublerInstance
  }

  private class XilinxClockDoubler(period: Double) extends ClockDoubler {
    val defn = ExtModule(info = NoInfo,
      name = getName("clock_doubler"),
      ports = Seq(
        Port(NoInfo,"CLKIN1",Input,ClockType),
        Port(NoInfo,"CLKFBIN",Input,ClockType),
        Port(NoInfo,"PWRDWN",Input,UIntType(IntWidth(1))),
        Port(NoInfo,"RST",Input,UIntType(IntWidth(1))),
        Port(NoInfo,"LOCKED",Output,UIntType(IntWidth(1))),
        Port(NoInfo,"CLKFBOUT",Output,ClockType),
        Port(NoInfo,"CLKFBOUTB",Output,ClockType),
        Port(NoInfo,"CLKOUT0",Output,ClockType),
        Port(NoInfo,"CLKOUT0B",Output,ClockType),
        Port(NoInfo,"CLKOUT1",Output,ClockType),
        Port(NoInfo,"CLKOUT1B",Output,ClockType),
        Port(NoInfo,"CLKOUT2",Output,ClockType),
        Port(NoInfo,"CLKOUT2B",Output,ClockType),
        Port(NoInfo,"CLKOUT3",Output,ClockType),
        Port(NoInfo,"CLKOUT3B",Output,ClockType),
        Port(NoInfo,"CLKOUT4",Output,ClockType),
        Port(NoInfo,"CLKOUT4B",Output,ClockType),
        Port(NoInfo,"CLKOUT5",Output,ClockType),
        Port(NoInfo,"CLKOUT5B",Output,ClockType),
        Port(NoInfo,"CLKOUT6",Output,ClockType),
        Port(NoInfo,"CLKOUT6B",Output,ClockType)),
      defname = "MMCME2_BASE",
      params = Seq(
        DoubleParam("CLKIN1_PERIOD",period),
        DoubleParam("CLKFBOUT_MULT_F",2.0)))

    private def instSubField(iname: String, pname: String, tpe: Type) = SubField(Reference(iname,ModuleBundleType(defn)),pname,tpe)

    def double(slowClock: Expression) = {
      val inst = DefInstance(NoInfo,getName(defn.name + "_inst"),defn.name)
      val inputExp = instSubField(inst.name,"CLKIN1",ClockType)
      val outputExp = instSubField(inst.name,"CLKOUT0",ClockType)
      val statements = immutable.Seq(
        inst,
        Connect(NoInfo,inputExp,slowClock),
        Connect(NoInfo,instSubField(inst.name,"CLKFBIN",ClockType),instSubField(inst.name,"CLKFBOUT",ClockType)),
        Connect(NoInfo,instSubField(inst.name,"PWRDWN",UIntType(IntWidth(1))),UIntLiteral(0,IntWidth(1))),
        Connect(NoInfo,instSubField(inst.name,"RST",UIntType(IntWidth(1))),UIntLiteral(0,IntWidth(1))))
      ClockDoublerInstance(statements,slowClock,outputExp)
    }
  }

  private def getRef(r: DefRegister) = Reference(r.name, r.tpe)
  private def getRef(w: DefWire) = Reference(w.name, w.tpe)
  
  private def alignPortCmd(
    clock: Expression,
    reset: Expression,
    nCycles: Int,
    port: MemPort,
    mem: DefMemory) = {
    val statements = new mutable.ArrayBuffer[Statement]
    // get command from port, connect to wire
    val portCmdType = MemType.cmdType(port,mem)
    val portCmd = DefWire(NoInfo,getName(port.name + "_cmd"),portCmdType)
    statements += portCmd
    statements += PartialConnect(NoInfo,getRef(portCmd),Reference(port.name,MemType.portType(port,mem)))
    // make null command to initialize alignment regs
    val initval = DefWire(NoInfo,getName(port.name + "_cmd_init"),portCmdType)
    statements += initval
    statements += IsInvalid(NoInfo,getRef(initval))
    statements += Connect(
      NoInfo,
      SubField(getRef(initval),"en",UIntType(IntWidth(1))),
      UIntLiteral(0,IntWidth(1)))
    // make a chain of nCycles (may be 0) registers delaying the command
    var currentRef = getRef(portCmd)
    for (d <- 1 to nCycles) {
      val alignReg = DefRegister(
        NoInfo,
        getName(port.name + "_cmd_r" + d),
        portCmdType,
        clock,
        reset,
        getRef(initval))
      val regRef = getRef(alignReg)
      statements += alignReg
      statements += Connect(NoInfo,regRef,currentRef)
      currentRef = regRef
    }
    // partial connect the last element in the chain to the fast mem port
    val fastMemPortRef = SubField(Reference(mem.name,MemType(mem)),port.name,MemType.portType(port,mem))
    statements += PartialConnect(NoInfo,fastMemPortRef,currentRef)
    statements.toSeq
  }

  private def alignPortResp(
    clock: Expression,
    reset: Expression,
    nCycles: Int,
    port: MemPort,
    mem: DefMemory) = {
    val statements = new mutable.ArrayBuffer[Statement]
    port match {
      case ReadPort(_) | ReadWritePort(_) =>
        val rdata_name = port match {
          case ReadPort(_) => "data"
          case ReadWritePort(_) => "rdata"
        }
        val initval = DefWire(NoInfo,getName(port.name + "_rdata_init"),mem.dataType)
        statements += initval
        statements += IsInvalid(NoInfo,getRef(initval))
        // make a chain of nCycles (may be 0) registers delaying the command
        var currentExp: Expression = SubField(SubField(Reference(mem.name,MemType(mem)),port.name,MemType.portType(port,mem)),rdata_name,mem.dataType)
        for (d <- 1 to nCycles) {
          val alignReg = DefRegister(
            NoInfo,
            getName(port.name + "_rdata_r" + d),
            mem.dataType,
            clock,
            reset,
            getRef(initval))
          val regRef = getRef(alignReg)
          statements += alignReg
          statements += Connect(NoInfo,regRef,currentExp)
          currentExp = regRef
        }
        // partial connect the last element in the chain to the fast mem port
        val slowPortRef = SubField(Reference(port.name,MemType.portType(port,mem)),rdata_name,mem.dataType)
        statements += Connect(NoInfo,slowPortRef,currentExp)
      case _ =>
    }
    statements.toSeq
  }

  private def defineMemWrapper(
    m: DefMemory,
    clockDoubler: ClockDoubler) = {
    // create DefModule defining double-pumped memory
    assert(m.readwriters.size == 0)
    assert((m.readers.size + m.writers.size) == 2)
    val memPorts: Seq[MemPort] = m.readers.map(ReadPort(_)) ++ m.writers.map(WritePort(_))
    val modulePorts = memPorts.map(p => Port(NoInfo,p.name,Input,MemType.portType(p,m)))
    val slowClockRef = SubField(Reference(modulePorts.head.name,modulePorts.head.tpe),"clk",ClockType)
    // TODO: handle reset
    // val reset = Reference("reset",Input,UIntType(IntWidth(1)))
    val reset = UIntLiteral(0,IntWidth(1))
    val delays = memPorts.zipWithIndex.toMap
    val maxDelay = delays.values.max
    // generate statements for wiring
    val doublerWiring = clockDoubler.double(slowClockRef)
    val fastMem = m
    val portClocks = memPorts.map(p => SubField(SubField(Reference(fastMem.name,MemType(fastMem)),p.name,MemType.portType(p,m)),"clk",ClockType))
    val connectClocks = portClocks.map(pClock => Connect(NoInfo,pClock,doublerWiring.fastClock))
    val alignCmds = memPorts.flatMap(p => alignPortCmd(doublerWiring.fastClock,reset,delays(p),p,m))
    val alignResps = memPorts.flatMap(p => alignPortResp(doublerWiring.fastClock,reset,maxDelay - delays(p),p,m))
    val moduleBody = Block((doublerWiring.statements :+ fastMem) ++ connectClocks ++ alignCmds ++ alignResps)
    val memModule = Module(
      m.info,
      getName(m.name + "_wrapper"),
      modulePorts, // TODO: handle reset modulePorts +: Port(NoInfo,"reset",Input,UIntType(IntWidth(1))),
      moduleBody)
    memModule
  }

  private def doublePump(
    m: DefMemory,
    reset: Expression,
    memModules: mutable.Buffer[DefModule],
    clockDoubler: ClockDoubler) = {
    val memWrapper = defineMemWrapper(m,clockDoubler)
    memModules += memWrapper
    // replace DefMemory with DefInstance
    DefInstance(m.info,m.name,memWrapper.name)
  }

  private def transformMems(
    reset: Expression,
    memModules: mutable.Buffer[DefModule],
    clockDoubler: ClockDoubler)(s: Statement): Statement = s match {
    case m: DefMemory =>
      if (m.writeLatency == 1 && m.readLatency == 1 &&
        (m.readers ++ m.writers ++ m.readwriters).length == 2) {
        doublePump(m,reset,memModules,clockDoubler)
      } else {
        m
      }
    case x => x map transformMems(reset,memModules,clockDoubler)
  }

  private def findResets(
    m: DefModule,
    resets: mutable.HashMap[DefModule,Expression])(s: Statement): Statement = s match {
    case r: DefRegister =>
      resets(m) = r.reset
      r
    case x => x map findResets(m,resets)
  }


  def run(c: Circuit): Circuit = {
    // Heuristic to find a reset in the module. TODO (magyar): make this more robust
    val resets = new mutable.HashMap[DefModule,Expression]
    c.modules map (m => m map findResets(m,resets))
    assert(resets.size > 0)

    // Create a clock doubler, period in ns
    val clockDoubler = new XilinxClockDoubler(50)

    // Transform memories
    val memModules = new mutable.ArrayBuffer[DefModule]
    val transformedModules = c.modules map (m => m map transformMems(resets(m),memModules,clockDoubler))
    c.copy(modules = transformedModules ++ memModules.toSeq :+ clockDoubler.defn)
  }

}
 
