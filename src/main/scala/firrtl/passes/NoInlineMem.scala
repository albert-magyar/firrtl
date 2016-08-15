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

class ConfWriter(filename: String) {
  val outputBuffer = new java.io.CharArrayWriter
  def addMem(bbname: String, m: DefMemory) = {
    val confPorts = (m.readers.map(p =>"r") ++
      m.writers.map(p => "w") ++
      m.readwriters.map(p => "rw")).mkString(",")
    outputBuffer.append(s"name ${bbname} depth ${m.depth} width ${bitWidth(m.dataType)} ports ${confPorts}\n")
  }
  def serialize = {
    val outputFile = new java.io.PrintWriter(filename)
    outputFile.write(outputBuffer.toString)
    outputFile.close()
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

class NoInlineMemPass(confWriter: ConfWriter) extends Pass {
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
      fromBits(WSubField(aggPort,"data",aggMem.dataType,UNKNOWNGENDER),
        WSubField(groundPort,"data",groundMem.dataType,UNKNOWNGENDER))
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
      fromBits(WSubField(aggPort,"rdata",aggMem.dataType,UNKNOWNGENDER),
        WSubField(groundPort,"rdata",groundMem.dataType,UNKNOWNGENDER)),
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
        val rconns = (k.readers zip loweredMem.readers).map{ case (x,y) =>
          adaptReader(WRef(x, UnknownType, PortKind(), UNKNOWNGENDER),
            k, WSubField(bbRef,y,UnknownType,UNKNOWNGENDER), loweredMem) }
        val wconns = (k.writers zip loweredMem.writers).map{ case (x,y) =>
          adaptWriter(WRef(x, UnknownType, PortKind(), UNKNOWNGENDER),
            k, WSubField(bbRef,y,UnknownType,UNKNOWNGENDER), loweredMem) }
        val rwconns = (k.writers zip loweredMem.writers).map{ case (x,y) =>
          adaptReadWriter(WRef(x, UnknownType, PortKind(), UNKNOWNGENDER),
            k, WSubField(bbRef,y,UnknownType,UNKNOWNGENDER), loweredMem) }
        Module(ExtMemInfo(k), v, ioPorts, Block(Seq(bbInst) ++ rconns ++ wconns))
      }
    }
    val memBlackboxModules = memBlackboxes map {
      case (k,v) => {
        val ioPorts = MemUtils.memToBundle(k).fields.map(f => Port(NoInfo, f.name, Input, f.tpe))
        val confPorts = (k.readers.map(x => "r") ++ k.writers.map(x => "w")).mkString(",")
        confWriter.addMem(v,k)
        ExtModule(ExtMemInfo(k), v, ioPorts)
      }
    }
    confWriter.serialize
    Circuit(c.info, transformedModules ++ memWrapperModules ++ memBlackboxModules, c.main)
  }
}

class NoInlineMem(transID: TransID) extends Transform with LazyLogging {
  def execute(circ: Circuit, map: AnnotationMap) = {
    map get transID match {
      case Some(p) => {
        p get CircuitName(circ.main) match {
          case Some(NoInlineMemAnnotation(_, _)) => {
            val writer = new ConfWriter(s"${circ.main}.conf")
            TransformResult((Seq(
              new NoInlineMemPass(writer),
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

