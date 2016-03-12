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

object CanonicalizeMemPorts extends Pass {
  def name = "CanonicalizeMemPorts"
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
  def bulkConnect(a: String, b: String) = BulkConnect(
    NoInfo,
    Ref(a, UnknownType()),
    Ref(b, UnknownType()))
  def simplifyMem(s: DefMemory): Stmt = {
    val rp = s.readers.zipWithIndex.map("r" + _._2)
    val wp = s.writers.zipWithIndex.map("w" + _._2)
    val rwp = s.readwriters.zipWithIndex.map("rw" + _._2)
    val adapter = DefWire(s.info, s.name, memToBundle(s))
    val simpleMem = s.copy(readers = rp, writers = wp, readwriters = rwp)
    val rconn = (rp, s.readers).zipped.map(bulkConnect(_,_))
    val wconn = (rp, s.writers).zipped.map(bulkConnect(_,_))
    val rwconn = (rp, s.readwriters).zipped.map(bulkConnect(_,_))
    val block = Seq(adapter, simpleMem) ++ rconn ++ wconn ++ rwconn
    return Begin(block)
  }
  def run(c: Circuit): Circuit = c
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
    ioMap.put(memModuleName,CanonicalizeMemPorts.memToBundle(mem))
    DefInstance(mem.info, mem.name, memModuleName) 
  }
}
