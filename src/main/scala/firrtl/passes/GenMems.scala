/*
Copyright (c) 2014 - 2016 The Regents of the University of
California (Regents). All Rights Reserved.  Redistribution and use in
source and binary forms, with or without modification, are permitted
provided that the following conditions are met:
   * Redistributions of source code must retain the above
     copyright notice, this list of conditions and the following
     two paragraphs of disclaimer.
   * Redistributions in binary form must reproduce the above
     copyright notice, this list of conditions and the following
     two paragraphs of disclaimer in the documentation and/or other materials
     provided with the distribution.
   * Neither the name of the Regents nor the names of its contributors
     may be used to endorse or promote products derived from this
     software without specific prior written permission.
IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT,
SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS,
ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF
REGENTS HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF
ANY, PROVIDED HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION
TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
MODIFICATIONS.
*/

package firrtl.passes

import com.typesafe.scalalogging.LazyLogging

import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.LinkedHashMap
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Serialize._
import firrtl.PrimOps._
import firrtl.WrappedExpression._

object toBits {
  def apply(e: Expression): Expression = {
    e match {
      case ex: Reference => hiercat(ex,ex.tpe)
      case ex: SubField => hiercat(ex,ex.tpe)
      case ex: SubIndex => hiercat(ex,ex.tpe)
      case t => error("Invalid operand expression for toBits!")
    }
  }
  def hiercat(e: Expression, dt: Type): Expression = {
    dt match {
      case t:VectorType => DoPrim(PrimOps.Cat, (0 to t.size).map(i => hiercat(SubIndex(e, i, t.tpe),t.tpe)), Seq.empty[BigInt], UnknownType)
      case t:BundleType => DoPrim(PrimOps.Cat, t.fields.map(f => hiercat(SubField(e, f.name, f.tpe),f.tpe)), Seq.empty[BigInt], UnknownType)
      case t:UIntType => e
      case t:SIntType => e
      case t => error("Unknown type encountered in toBits!")
    }
  }
}

object bitWidth {
  def apply(dt: Type): BigInt = widthOf(dt)
  def widthOf(dt: Type): BigInt = {
    dt match {
      case t:VectorType => t.size * bitWidth(t.tpe)
      case t:BundleType => t.fields.map(f => bitWidth(f.tpe)).foldLeft(BigInt(0))(_+_)
      case t:UIntType => baseWidth(t.width)
      case t:SIntType => baseWidth(t.width)
      case t => error("Unknown type encountered in bitWidth!")
    }
  }
  def baseWidth(w: Width): BigInt = {
   w match {
     case w:IntWidth => w.width
     case w => error("Unknown width encountered in bitWidth!")
   }
  }
}

object fromBits {
  def apply(lhs: Expression, rhs: Expression): Statement = {
    val fbits = lhs match {
      case ex: Reference => getPart(ex,ex.tpe,rhs,0)
      case ex: SubField => getPart(ex,ex.tpe,rhs,0)
      case ex: SubIndex => getPart(ex,ex.tpe,rhs,0)
      case t => error("Invalid LHS expression for fromBits!")
    }
    Block(fbits._2)
  }
  def getPartGround(lhs: Expression, lhst: Type, rhs: Expression, offset: BigInt): (BigInt, Seq[Statement]) = {
    val intWidth = bitWidth(lhst)
    val sel = DoPrim(PrimOps.Bits,Seq(rhs),Seq(offset+intWidth-1,offset),UnknownType)
    (offset + intWidth, Seq(Connect(NoInfo,lhs,sel)))
  }
  def getPart(lhs: Expression, lhst: Type, rhs: Expression, offset: BigInt): (BigInt, Seq[Statement]) = {
    lhst match {
      case t:VectorType => {
        var currentOffset = offset
        var stmts = Seq.empty[Statement]
        for (i <- (0 to t.size)) {
          val (tmpOffset, substmts) = getPart(SubIndex(lhs, i, t.tpe), t.tpe, rhs, currentOffset)
          stmts = stmts ++ substmts
          currentOffset = tmpOffset
        }
        (currentOffset, stmts)
      }
      case t:BundleType => {
        var currentOffset = offset
        var stmts = Seq.empty[Statement]
        for (f <- t.fields.reverse) {
          println("Resolving field " + f.name)
          val (tmpOffset, substmts) = getPart(SubField(lhs, f.name, f.tpe), f.tpe, rhs, currentOffset)
          stmts = stmts ++ substmts
          currentOffset = tmpOffset
        }
        (currentOffset, stmts)
      }
      case t:UIntType => getPartGround(lhs,t,rhs,offset)
      case t:SIntType => getPartGround(lhs,t,rhs,offset)
      case t => error("Unknown type encountered in fromBits!")
    }
  }
}

object MemUtils {
  def rPortToBundle(name: String, mem: DefMemory) =
    BundleType(Seq(
      Field("data", Flip, mem.dataType),
      Field("addr", Default, UIntType(IntWidth(ceil_log2(mem.depth)))),
      Field("en", Default, UIntType(IntWidth(1))),
      Field("clk", Default, ClockType)))
  def wPortToBundle(name: String, mem: DefMemory) =
    BundleType(Seq(
      Field("data", Default, mem.dataType),
      Field("mask", Default, create_mask(mem.dataType)),
      Field("addr", Default, UIntType(IntWidth(ceil_log2(mem.depth)))),
      Field("en", Default, UIntType(IntWidth(1))),
      Field("clk", Default, ClockType)))
  def rwPortToBundle(name: String, mem: DefMemory) =
    BundleType(Seq(
      Field("rmode", Default, UIntType(IntWidth(1))),
      Field("data", Default, mem.dataType),
      Field("rdata", Flip, mem.dataType),
      Field("mask", Default, create_mask(mem.dataType)),
      Field("addr", Default, UIntType(IntWidth(ceil_log2(mem.depth)))),
      Field("en", Default, UIntType(IntWidth(1))),
      Field("clk", Default, ClockType)))
  def memToBundle(s: DefMemory) = BundleType(
    s.readers.map(p => Field(p, Default, rPortToBundle(p,s))) ++
      s.writers.map(p => Field(p, Default, wPortToBundle(p,s))) ++
      s.readwriters.map(p => Field(p, Default, rwPortToBundle(p,s))))
  def deepField(wire: String, fieldChain: Seq[String]): SubField = {
    if (fieldChain.length == 1) {
      SubField(Reference(wire, UnknownType), fieldChain.last, UnknownType)
    } else {
      SubField(deepField(wire, fieldChain.init), fieldChain.last, UnknownType)
    }
  }
  // TODO: this is totally wrong
  def bulkConnect(a: String, b: String) = Connect(
    NoInfo,
    Reference(a, UnknownType),
    Reference(b, UnknownType))
}

object ModularizeMems extends Pass {
  def name = "ModularizeMems"
  def memAdapters = LinkedHashSet[DefModule]()
  def run(c: Circuit) = c
}

object LowerMemTypes extends Pass {
  def name = "LowerMemTypes"
  def connectField(a: String, b: String, field: Seq[String]) =
    Connect(NoInfo,
      MemUtils.deepField(a,field),
      MemUtils.deepField(b,field))
  def adaptReader(aggPorts: DefWire, aggMem: DefMemory, groundMem: DefMemory, name: String): Statement = {
    val stmts = Seq(
      connectField(groundMem.name,aggPorts.name,Seq(name,"addr")),
      connectField(groundMem.name,aggPorts.name,Seq(name,"en")),
      connectField(groundMem.name,aggPorts.name,Seq(name,"clk")),
      fromBits(MemUtils.deepField(aggPorts.name,Seq(name,"data")).copy(tpe=aggMem.dataType),
        MemUtils.deepField(groundMem.name,Seq(name,"data")).copy(tpe=groundMem.dataType))
    )
    Block(stmts)
  }
  def adaptWriter(aggPorts: DefWire, aggMem: DefMemory, groundMem: DefMemory, name: String): Statement = {
    val stmts = Seq(
      connectField(groundMem.name,aggPorts.name,Seq(name,"addr")),
      connectField(groundMem.name,aggPorts.name,Seq(name,"en")),
      connectField(groundMem.name,aggPorts.name,Seq(name,"clk")),
      Connect(NoInfo,
        MemUtils.deepField(groundMem.name,Seq(name,"data")),
        toBits(MemUtils.deepField(aggPorts.name,Seq(name,"data")).copy(tpe=aggMem.dataType)))
    )
    Block(stmts)
  }
  def lowerMem(s: DefMemory, ns: Namespace): Statement = {
    assert(s.dataType != UnknownType)
    val adapter = DefWire(s.info, s.name, MemUtils.memToBundle(s))
    val simpleMem = s.copy(name=ns.newName(s.name), dataType=UIntType(IntWidth(bitWidth(s.dataType))))
    val rconns = s.readers.map(x => adaptReader(adapter, s, simpleMem, x))
    val wconns = s.writers.map(x => adaptWriter(adapter, s, simpleMem, x))
    Block(Seq(adapter,simpleMem) ++ rconns ++ wconns)
  }
  def transformMems(s: Statement, ns: Namespace): Statement = s match {
    case s: DefMemory => lowerMem(s,ns)
    case s => s map ((x: Statement) => transformMems(x,ns))
  }
  def run(c: Circuit): Circuit = {
    val transformedModules = c.modules.map {
      m => m match {
        case m: Module => {
          val ns = Namespace(m)
          val transformedBody = transformMems(m.body,ns)
          Module(m.info, m.name, m.ports, transformedBody)
        }
        case m: ExtModule => m
      }
    }
    Circuit(c.info,transformedModules,c.main)
  }
}

object CanonicalizeMemPorts extends Pass {
  def name = "CanonicalizeMemPorts"
  def simplifyMem(s: DefMemory, ns: Namespace): Statement = {
    val rp = s.readers.zipWithIndex.map("r" + _._2)
    val wp = s.writers.zipWithIndex.map("w" + _._2)
    val rwp = s.readwriters.zipWithIndex.map("rw" + _._2)
    val adapter = DefWire(s.info, s.name, MemUtils.memToBundle(s))
    val simpleMem = s.copy(name=ns.newName(s.name), readers=rp, writers=wp, readwriters=rwp)
    val rconn = (rp, s.readers).zipped.map((a,b) => MemUtils.bulkConnect(simpleMem.name + "." + a,
      adapter.name + "." + b))
    val wconn = (wp, s.writers).zipped.map((a,b) => MemUtils.bulkConnect(simpleMem.name + "." + a,
      adapter.name + "." + b))
    val rwconn = (rwp, s.readwriters).zipped.map((a,b) => MemUtils.bulkConnect(simpleMem.name + "." + a,
      adapter.name + "." + b))
    val block = Seq(adapter, simpleMem) ++ rconn ++ wconn ++ rwconn
    return Block(block)
  }
  def transformMems(s: Statement, ns: Namespace): Statement = s match {
    case s: DefMemory => simplifyMem(s,ns)
    case s => s map ((x: Statement) => transformMems(x,ns))
  }
  def run(c: Circuit): Circuit = {
    val transformedModules = c.modules.map {
      m => m match {
        case m: Module => {
          val ns = Namespace(m)
          val transformedBody = transformMems(m.body,ns)
          Module(m.info, m.name, m.ports, transformedBody)
        }
        case m: ExtModule => m
      }
    }
    Circuit(c.info,transformedModules,c.main)
  }
}

case class ExtMemInfo(mem: DefMemory) extends Info {
  override def toString = "Generated ExtMem"
}

object LowerExtMemTypes extends Pass {
  def name = "LowerExtMemTypes"
  def connectField(a: String, b: String, field: Seq[String]) =
    Connect(NoInfo,
      MemUtils.deepField(a,field),
      MemUtils.deepField(b,field))
  def adaptReader(mname: String, name: String, aggType: Type, groundType: Type): Statement = {
    val stmts = Seq(
      Connect(NoInfo,MemUtils.deepField(mname,Seq(name,"clk")),MemUtils.deepField(name,Seq("clk"))),
      Connect(NoInfo,MemUtils.deepField(mname,Seq(name,"addr")),MemUtils.deepField(name,Seq("addr"))),
      Connect(NoInfo,MemUtils.deepField(mname,Seq(name,"en")),MemUtils.deepField(name,Seq("en"))),
      fromBits(MemUtils.deepField(name,Seq("data")).copy(tpe=aggType),
        MemUtils.deepField(mname,Seq(name,"data")).copy(tpe=groundType))
    )
    Block(stmts)
  }
  def lowerExtMem(extMem: ExtModule, info: ExtMemInfo, ns: Namespace): Seq[DefModule] = {
    assert(info.mem.dataType != UnknownType)
    val groundType = UIntType(IntWidth(bitWidth(info.mem.dataType)))
    val groundMem = info.mem.copy(dataType=groundType)
    val groundPorts = MemUtils.memToBundle(groundMem)
      .fields.map(f => Port(NoInfo, f.name, Input, f.tpe))
    val newExtMem = extMem.copy(info=ExtMemInfo(groundMem),ports = groundPorts)
    val newExinst = DefInstance(NoInfo,"inner",newExtMem.name)
    val rconns = info.mem.readers.map(x => adaptReader(extMem.name, x, info.mem.dataType, groundType))
    val adapter = Module(
      info,
      ns.newName("mem_adapter"),
      extMem.ports,
      Block(Seq(newExinst) ++ rconns)
    )
    Seq(newExtMem,adapter)
  }
  def run(c: Circuit): Circuit = {
    val moduleNS = Namespace()
    c.modules.foreach(m => moduleNS.tryName(m.name))
    val transformedModules = ArrayBuffer[DefModule]()
    c.modules.foreach {
      m => m match {
        case m: Module => transformedModules += m
        case m: ExtModule => {
          m.info match {
            case info: ExtMemInfo => transformedModules ++= lowerExtMem(m,info,moduleNS)
            case info => transformedModules += m
          }
        }
      }
    }
    Circuit(c.info,transformedModules,c.main)
  }
}

object NoInlineMems extends Pass {
  def name = "NoInlineMems"
  def connectField(lhs: Expression, rhs: Expression, field: String) =
    Connect(NoInfo,
      SubField(lhs,field,UnknownType),
      SubField(rhs,field,UnknownType))
  def adaptReader(aggPort: Expression, aggMem: DefMemory, groundPort: Expression, groundMem: DefMemory): Statement = {
    val stmts = Seq(
      connectField(groundPort,aggPort,"addr"),
      connectField(groundPort,aggPort,"en"),
      connectField(groundPort,aggPort,"clk"),
      fromBits(SubField(aggPort,"data",aggMem.dataType),SubField(groundPort,"data",groundMem.dataType))
    )
    Block(stmts)
  }
  def adaptWriter(aggPort: Expression, aggMem: DefMemory, groundPort: Expression, groundMem: DefMemory): Statement = {
    val stmts = Seq(
      connectField(groundPort,aggPort,"addr"),
      connectField(groundPort,aggPort,"en"),
      connectField(groundPort,aggPort,"clk"),
      Connect(NoInfo,
        SubField(groundPort,"data",groundMem.dataType),
        toBits(SubField(aggPort,"data",aggMem.dataType)))
    )
    Block(stmts)
  }
  def run(c: Circuit): Circuit = {
    val memWrappers = LinkedHashMap[DefMemory,String]()
    val memBlackboxes = LinkedHashMap[DefMemory,String]()
    val moduleNS = Namespace()
    c.modules.foreach(m => moduleNS.tryName(m.name))
    def transformMems(s: Statement): Statement = s match {
      case s: DefMemory => {
        val memWrapperName = memWrappers.getOrElseUpdate(s.copy(),
          moduleNS.newName("mem_wrapper"))
        DefInstance(s.info, s.name, memWrapperName)
      }
      case s => s map (transformMems)
    }
    val transformedModules = c.modules.map {
      m => m match {
        case m: Module => {
          val transformedBody = transformMems(m.body)
          Module(m.info, m.name, m.ports, transformedBody)
        }
        case m: ExtModule => m
      } 
    }
    val memWrapperModules = memWrappers map {
      case (k,v) => {
        assert(k.dataType != UnknownType)
        val ioPorts = MemUtils.memToBundle(k).fields.map(f => Port(NoInfo, f.name, Input, f.tpe))
        val loweredMem = k.copy(dataType=UIntType(IntWidth(bitWidth(k.dataType))))
        val memBlackboxName = memBlackboxes.getOrElseUpdate(loweredMem.copy(),
          moduleNS.newName("mem_blackbox"))
        val bbInst = DefInstance(k.info, k.name, memBlackboxName)
        val bbRef = Reference(bbInst.name,UnknownType)
        val rconns = k.readers.map(x => adaptReader(Reference(x, UnknownType), k, SubField(bbRef,x,UnknownType), loweredMem))
        val wconns = k.writers.map(x => adaptWriter(Reference(x, UnknownType), k, SubField(bbRef,x,UnknownType), loweredMem))
        Module(ExtMemInfo(k), v, ioPorts, Block(Seq(bbInst) ++ rconns ++ wconns))
      }
    }
    val memBlackboxModules = memBlackboxes map {
      case (k,v) => {
        val ioPorts = MemUtils.memToBundle(k).fields.map(f => Port(NoInfo, f.name, Input, f.tpe))
        ExtModule(ExtMemInfo(k), v, ioPorts)
      }
    }
    Circuit(c.info, transformedModules ++ memWrapperModules ++ memBlackboxModules, c.main)
  }
}
