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
import firrtl.PrimOps._
import firrtl.Annotations._
import firrtl.WrappedExpression._

case class NoInlineMemAnnotation(t: String, tID: TransID)
    extends Annotation with Loose with Unstable {
  val target = CircuitName(t)
  def duplicate(n: Named) = this.copy(t=n.name)
}

object toBits {
  def apply(e: Expression): Expression = {
    e match {
      case ex: WRef => hiercat(ex,ex.tpe)
      case ex: WSubField => hiercat(ex,ex.tpe)
      case ex: WSubIndex => hiercat(ex,ex.tpe)
      case t => error("Invalid operand expression for toBits!")
    }
  }
  def hiercat(e: Expression, dt: Type): Expression = {
    dt match {
      case t:VectorType => DoPrim(PrimOps.Cat, (0 to t.size).map(i => hiercat(WSubIndex(e, i, t.tpe, UNKNOWNGENDER),t.tpe)), Seq.empty[BigInt], UIntType(UnknownWidth))
      case t:BundleType => DoPrim(PrimOps.Cat, t.fields.map(f => hiercat(WSubField(e, f.name, f.tpe, UNKNOWNGENDER),f.tpe)), Seq.empty[BigInt], UIntType(UnknownWidth))
      case t:UIntType => e
      case t:SIntType => e
      case t => error("Unknown type encountered in toBits!")
    }
  }
}

object toBitMask {
  def apply(e: Expression, dataType: Type): Expression = {
    e match {
      case ex: WRef => hiermask(ex,ex.tpe,dataType)
      case ex: WSubField => hiermask(ex,ex.tpe,dataType)
      case ex: WSubIndex => hiermask(ex,ex.tpe,dataType)
      case t => error("Invalid operand expression for toBits!")
    }
  }
  def hiermask(e: Expression, maskType: Type, dataType: Type): Expression = {
    (maskType, dataType) match {
      case (mt:VectorType, dt:VectorType) => DoPrim(PrimOps.Cat, (0 to mt.size).map(i => hiermask(WSubIndex(e, i, mt.tpe, UNKNOWNGENDER), mt.tpe, dt.tpe)), Seq.empty[BigInt], UIntType(UnknownWidth))
      case (mt:BundleType, dt:BundleType) => DoPrim(PrimOps.Cat, (mt.fields zip dt.fields).map{ case (mf,df) => hiermask(WSubField(e, mf.name, mf.tpe, UNKNOWNGENDER), mf.tpe, df.tpe) }, Seq.empty[BigInt], UIntType(UnknownWidth))
      case (mt:UIntType, dt) => groundBitMask(e, dt)
      case (mt, dt) => error("Invalid type for mask component!")
    }
  }
  def groundBitMask(e: Expression, dataType: Type): Expression = {
    dataType match {
      case dt:UIntType => DoPrim(PrimOps.Cat, List.fill(bitWidth(dt).intValue)(e), Seq.empty[BigInt], UIntType(UnknownWidth))
      case dt:SIntType => DoPrim(PrimOps.Cat, List.fill(bitWidth(dt).intValue)(e), Seq.empty[BigInt], UIntType(UnknownWidth))
      case dt => error("Mask type does not properly correspond with data type!")
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
      case ex: WRef => getPart(ex,ex.tpe,rhs,0)
      case ex: WSubField => getPart(ex,ex.tpe,rhs,0)
      case ex: WSubIndex => getPart(ex,ex.tpe,rhs,0)
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
          val (tmpOffset, substmts) = getPart(WSubIndex(lhs, i, t.tpe, UNKNOWNGENDER), t.tpe, rhs, currentOffset)
          stmts = stmts ++ substmts
          currentOffset = tmpOffset
        }
        (currentOffset, stmts)
      }
      case t:BundleType => {
        var currentOffset = offset
        var stmts = Seq.empty[Statement]
        for (f <- t.fields.reverse) {
          val (tmpOffset, substmts) = getPart(WSubField(lhs, f.name, f.tpe, UNKNOWNGENDER), f.tpe, rhs, currentOffset)
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
      Field("wmode", Default, UIntType(IntWidth(1))),
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

object NoInlineMemPass extends Pass {
  def name = "NoInlineMem"
  def connectField(lhs: Expression, rhs: Expression, field: String) =
    Connect(NoInfo,
      WSubField(lhs,field,UnknownType,UNKNOWNGENDER),
      WSubField(rhs,field,UnknownType,UNKNOWNGENDER))
  def adaptReader(aggPort: Expression, aggMem: DefMemory, groundPort: Expression, groundMem: DefMemory): Statement = {
    val stmts = Seq(
      connectField(groundPort,aggPort,"addr"),
      connectField(groundPort,aggPort,"en"),
      connectField(groundPort,aggPort,"clk"),
      fromBits(WSubField(aggPort,"data",aggMem.dataType,UNKNOWNGENDER),WSubField(groundPort,"data",groundMem.dataType,UNKNOWNGENDER))
    )
    Block(stmts)
  }
  def adaptWriter(aggPort: Expression, aggMem: DefMemory, groundPort: Expression, groundMem: DefMemory): Statement = {
    val stmts = Seq(
      connectField(groundPort,aggPort,"addr"),
      connectField(groundPort,aggPort,"en"),
      connectField(groundPort,aggPort,"clk"),
      Connect(NoInfo,
        WSubField(groundPort,"data",groundMem.dataType,UNKNOWNGENDER),
        toBits(WSubField(aggPort,"data",aggMem.dataType,UNKNOWNGENDER))),
      Connect(NoInfo,
        WSubField(groundPort,"mask",create_mask(groundMem.dataType),UNKNOWNGENDER),
        toBitMask(WSubField(aggPort,"mask",create_mask(aggMem.dataType),UNKNOWNGENDER),aggMem.dataType))
    )
    Block(stmts)
  }
  def adaptReadWriter(aggPort: Expression, aggMem: DefMemory, groundPort: Expression, groundMem: DefMemory): Statement = {
    val stmts = Seq(
      connectField(groundPort,aggPort,"addr"),
      connectField(groundPort,aggPort,"en"),
      connectField(groundPort,aggPort,"wmode"),
      connectField(groundPort,aggPort,"clk"),
      fromBits(WSubField(aggPort,"rdata",aggMem.dataType,UNKNOWNGENDER),WSubField(groundPort,"rdata",groundMem.dataType,UNKNOWNGENDER)),
      Connect(NoInfo,
        WSubField(groundPort,"data",groundMem.dataType,UNKNOWNGENDER),
        toBits(WSubField(aggPort,"data",aggMem.dataType,UNKNOWNGENDER))),
      Connect(NoInfo,
        WSubField(groundPort,"mask",create_mask(groundMem.dataType),UNKNOWNGENDER),
        toBitMask(WSubField(aggPort,"mask",create_mask(aggMem.dataType),UNKNOWNGENDER),aggMem.dataType))
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
        WDefInstance(s.info, s.name, memWrapperName, UnknownType)
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
        val bbInst = WDefInstance(k.info, k.name, memBlackboxName,UnknownType)
        val bbRef = WRef(bbInst.name,UnknownType,InstanceKind(),UNKNOWNGENDER)
        val rconns = (k.readers zip loweredMem.readers).map{ case (x,y) => adaptReader(WRef(x, UnknownType, PortKind(), UNKNOWNGENDER), k, WSubField(bbRef,y,UnknownType,UNKNOWNGENDER), loweredMem) }
        val wconns = (k.writers zip loweredMem.writers).map{ case (x,y) => adaptWriter(WRef(x, UnknownType, PortKind(), UNKNOWNGENDER), k, WSubField(bbRef,y,UnknownType,UNKNOWNGENDER), loweredMem) }
        val rwconns = (k.writers zip loweredMem.writers).map{ case (x,y) => adaptReadWriter(WRef(x, UnknownType, PortKind(), UNKNOWNGENDER), k, WSubField(bbRef,y,UnknownType,UNKNOWNGENDER), loweredMem) }
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

class NoInlineMem(transID: TransID) extends Transform with LazyLogging {
  def execute(circ: Circuit, map: AnnotationMap) = {
    println(map.toString)
    println(transID.toString)
    println(map.get(transID).toString)
    map get transID match {
      case Some(p) => {
        p get CircuitName(circ.main) match {
          case Some(NoInlineMemAnnotation(_, _)) => {
            TransformResult((Seq(
              NoInlineMemPass,
              CheckInitialization,
              ResolveKinds,
              InferTypes,
              ResolveGenders) foldLeft circ){ (c, pass) =>
              val x = Utils.time(pass.name)(pass run c)
              logger debug x.serialize
              x
            }, None, Some(map))
          }
          case _ => TransformResult(circ, None, Some(map))
        }
      }
      case _ => TransformResult(circ, None, Some(map))
    }
  }
}

