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

import firrtl._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.Serialize._
import firrtl.PrimOps._
import firrtl.WrappedExpression._

object toBits {
  def apply(e: Expression): Expression = {
    e match {
      case ex: Ref => hiercat(ex,ex.tpe)
      case ex: SubField => hiercat(ex,ex.tpe)
      case ex: SubIndex => hiercat(ex,ex.tpe)
      case t => error("Invalid operand expression for toBits!")
    }
  }
  def hiercat(e: Expression, dt: Type): Expression = {
    dt match {
      case t:VectorType => DoPrim(CONCAT_OP, (0 to t.size).map(i => hiercat(SubIndex(e, i, t.tpe),t.tpe)), Seq.empty[BigInt], UnknownType())
      case t:BundleType => DoPrim(CONCAT_OP, t.fields.map(f => hiercat(SubField(e, f.name, f.tpe),f.tpe)), Seq.empty[BigInt], UnknownType())
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
  def apply(lhs: Expression, rhs: Expression): Stmt = {
    val fbits = lhs match {
      case ex: Ref => getPart(ex,ex.tpe,rhs,0)
      case ex: SubField => getPart(ex,ex.tpe,rhs,0)
      case ex: SubIndex => getPart(ex,ex.tpe,rhs,0)
      case t => error("Invalid LHS expression for fromBits!")
    }
    Begin(fbits._2)
  }
  def getPartGround(lhs: Expression, lhst: Type, rhs: Expression, offset: BigInt): (BigInt, Seq[Stmt]) = {
    val intWidth = bitWidth(lhst)
    val sel = DoPrim(BITS_SELECT_OP,Seq(rhs),Seq(offset+intWidth-1,offset),UnknownType())
    (offset + intWidth, Seq(Connect(NoInfo,lhs,sel)))
  }
  def getPart(lhs: Expression, lhst: Type, rhs: Expression, offset: BigInt): (BigInt, Seq[Stmt]) = {
    lhst match {
      case t:VectorType => {
        var currentOffset = offset
        var stmts = Seq.empty[Stmt]
        for (i <- (0 to t.size)) {
          val (tmpOffset, substmts) = getPart(SubIndex(lhs, i, t.tpe), t.tpe, rhs, currentOffset)
          stmts = stmts ++ substmts
          currentOffset = tmpOffset
        }
        (currentOffset, stmts)
      }
      case t:BundleType => {
        var currentOffset = offset
        var stmts = Seq.empty[Stmt]
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
      Field("data", REVERSE, mem.data_type),
      Field("addr", DEFAULT, UIntType(IntWidth(ceil_log2(mem.depth)))),
      Field("en", DEFAULT, UIntType(IntWidth(1))),
      Field("clk", DEFAULT, ClockType())))
  def wPortToBundle(name: String, mem: DefMemory) =
    BundleType(Seq(
      Field("data", DEFAULT, mem.data_type),
      Field("mask", DEFAULT, create_mask(mem.data_type)),
      Field("addr", DEFAULT, UIntType(IntWidth(ceil_log2(mem.depth)))),
      Field("en", DEFAULT, UIntType(IntWidth(1))),
      Field("clk", DEFAULT, ClockType())))
  def rwPortToBundle(name: String, mem: DefMemory) =
    BundleType(Seq(
      Field("rmode", DEFAULT, UIntType(IntWidth(1))),
      Field("data", DEFAULT, mem.data_type),
      Field("rdata", REVERSE, mem.data_type),
      Field("mask", DEFAULT, create_mask(mem.data_type)),
      Field("addr", DEFAULT, UIntType(IntWidth(ceil_log2(mem.depth)))),
      Field("en", DEFAULT, UIntType(IntWidth(1))),
      Field("clk", DEFAULT, ClockType())))
  def memToBundle(s: DefMemory) = BundleType(
    s.readers.map(p => Field(p, DEFAULT, rPortToBundle(p,s))) ++
      s.writers.map(p => Field(p, DEFAULT, wPortToBundle(p,s))) ++
      s.readwriters.map(p => Field(p, DEFAULT, rwPortToBundle(p,s))))
  def deepField(wire: String, fieldChain: Seq[String]): SubField = {
    if (fieldChain.length == 1) {
      SubField(Ref(wire, UnknownType()), fieldChain.last, UnknownType())
    } else {
      SubField(deepField(wire, fieldChain.init), fieldChain.last, UnknownType())
    }
  }
  // TODO: this is totally wrong
  def bulkConnect(a: String, b: String) = BulkConnect(
    NoInfo,
    Ref(a, UnknownType()),
    Ref(b, UnknownType()))
}

object LowerMemTypes extends Pass {
  def name = "LowerMemTypes"
  def connectField(a: String, b: String, field: Seq[String]) =
    Connect(NoInfo,
      MemUtils.deepField(a,field),
      MemUtils.deepField(b,field))
  def adaptReader(aggPorts: DefWire, aggMem: DefMemory, groundMem: DefMemory, name: String): Stmt = {
    val stmts = Seq(
      connectField(groundMem.name,aggPorts.name,Seq(name,"addr")),
      connectField(groundMem.name,aggPorts.name,Seq(name,"en")),
      connectField(groundMem.name,aggPorts.name,Seq(name,"clk")),
      fromBits(MemUtils.deepField(aggPorts.name,Seq(name,"data")).copy(tpe=aggMem.data_type),
        MemUtils.deepField(groundMem.name,Seq(name,"data")).copy(tpe=groundMem.data_type))
    )
    Begin(stmts)
  }
  def adaptWriter(aggPorts: DefWire, aggMem: DefMemory, groundMem: DefMemory, name: String): Stmt = {
    val stmts = Seq(
      connectField(groundMem.name,aggPorts.name,Seq(name,"addr")),
      connectField(groundMem.name,aggPorts.name,Seq(name,"en")),
      connectField(groundMem.name,aggPorts.name,Seq(name,"clk")),
      Connect(NoInfo,
        MemUtils.deepField(groundMem.name,Seq(name,"data")),
        toBits(MemUtils.deepField(aggPorts.name,Seq(name,"data")).copy(tpe=aggMem.data_type)))
    )
    Begin(stmts)
  }
  def lowerMem(s: DefMemory, ns: Namespace): Stmt = {
    assert(!(s.data_type.isInstanceOf[UnknownType]))
    val adapter = DefWire(s.info, s.name, MemUtils.memToBundle(s))
    val simpleMem = s.copy(name=ns.newName(s.name), data_type=UIntType(IntWidth(bitWidth(s.data_type))))
    val rconns = s.readers.map(x => adaptReader(adapter, s, simpleMem, x))
    val wconns = s.writers.map(x => adaptWriter(adapter, s, simpleMem, x))
    Begin(Seq(adapter,simpleMem) ++ rconns ++ wconns)
  }
  def transformMems(s: Stmt, ns: Namespace): Stmt = s match {
    case s: DefMemory => lowerMem(s,ns)
    case s => s map ((x: Stmt) => transformMems(x,ns))
  }
  def run(c: Circuit): Circuit = {
    val transformedModules = c.modules.map {
      m => m match {
        case m: InModule => {
          val ns = Namespace(m)
          val transformedBody = transformMems(m.body,ns)
          InModule(m.info, m.name, m.ports, transformedBody)
        }
        case m: ExModule => m
      }
    }
    Circuit(c.info,transformedModules,c.main)
  }
}

object CanonicalizeMemPorts extends Pass {
  def name = "CanonicalizeMemPorts"
  def simplifyMem(s: DefMemory, ns: Namespace): Stmt = {
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
    return Begin(block)
  }
  def transformMems(s: Stmt, ns: Namespace): Stmt = s match {
    case s: DefMemory => simplifyMem(s,ns)
    case s => s map ((x: Stmt) => transformMems(x,ns))
  }
  def run(c: Circuit): Circuit = {
    val transformedModules = c.modules.map {
      m => m match {
        case m: InModule => {
          val ns = Namespace(m)
          val transformedBody = transformMems(m.body,ns)
          InModule(m.info, m.name, m.ports, transformedBody)
        }
        case m: ExModule => m
      }
    }
    Circuit(c.info,transformedModules,c.main)
  }
}

trait GenMems extends Pass {
  def run(c: Circuit): Circuit = {
    val memExModuleUIDs = LinkedHashSet[String]()
    def transformMems(s: Stmt): Stmt = s match {
      case s: DefMemory => {
        val exModuleInstance = emitExMemoryInstance(s)
        memExModuleUIDs += exModuleInstance.name
        exModuleInstance
      }
      case s => s map (transformMems)
    }
    val transformedModules = c.modules.map {
      m => m match {
        case m: InModule => {
          val transformedBody = transformMems(m.body)
          InModule(m.info, m.name, m.ports, transformedBody)
        }
        case m: ExModule => m
      } 
    }
    val memExModules = memExModuleUIDs map {
      uid => emitExMemoryModule(uid)
    }
    Circuit(c.info, transformedModules ++ memExModules, c.main)
  }
  def emitExMemoryModule(uid: String): ExModule
  def emitExMemoryInstance(mem: DefMemory): DefInstance
}

object TestNoInlineMems extends GenMems {
  def name = "TestNoInlineMems"
  val ioMap = LinkedHashMap[String,BundleType]()
  var memID = 0
  def emitExMemoryModule(uid: String): ExModule = {
    val ioPorts = ioMap(uid).fields.map(f => Port(NoInfo, f.name, INPUT, f.tpe))
    ExModule(NoInfo, uid, ioPorts)
  }
  def emitExMemoryInstance(mem: DefMemory): DefInstance = {
    val memModuleName = "mem" + memID
    memID = memID + 1
    ioMap.put(memModuleName,MemUtils.memToBundle(mem))
    DefInstance(mem.info, mem.name, memModuleName) 
  }
}
