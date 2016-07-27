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
}

case class ExtMemInfo(mem: DefMemory) extends Info {
  override def toString = "Generated memory wrapper"
}

object NoInlineMem extends Pass {
  def name = "NoInlineMem"
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
        val loweredMem = k.copy(dataType=UIntType(IntWidth(bitWidth(k.dataType))),
          readers=k.readers.zipWithIndex.map{ case (x,i) => s"R$i" },
          writers=k.writers.zipWithIndex.map{ case (x,i) => s"W$i" })
        val memBlackboxName = memBlackboxes.getOrElseUpdate(loweredMem.copy(),
          moduleNS.newName("mem_blackbox"))
        val bbInst = DefInstance(k.info, k.name, memBlackboxName)
        val bbRef = Reference(bbInst.name,UnknownType)
        val rconns = (k.readers zip loweredMem.readers).map{ case (x,y) => adaptReader(Reference(x, UnknownType), k, SubField(bbRef,y,UnknownType), loweredMem) }
        val wconns = (k.writers zip loweredMem.writers).map{ case (x,y) => adaptWriter(Reference(x, UnknownType), k, SubField(bbRef,y,UnknownType), loweredMem) }
        Module(ExtMemInfo(k), v, ioPorts, Block(Seq(bbInst) ++ rconns ++ wconns))
      }
    }
    val memBlackboxModules = memBlackboxes map {
      case (k,v) => {
        val ioPorts = MemUtils.memToBundle(k).fields.map(f => Port(NoInfo, f.name, Input, f.tpe))
        val confPorts = (k.readers.map(x => "r") ++ k.writers.map(x => "w")).mkString(",")
        println(s"name ${k.name} depth ${k.depth} width ${bitWidth(k.dataType)} ports ${confPorts}")
        ExtModule(ExtMemInfo(k), v, ioPorts)
      }
    }
    Circuit(c.info, transformedModules ++ memWrapperModules ++ memBlackboxModules, c.main)
  }
}
