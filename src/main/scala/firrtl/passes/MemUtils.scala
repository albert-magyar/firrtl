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
      case t:VectorType => DoPrim(PrimOps.Cat, (0 to t.size).map(i =>
          hiercat(WSubIndex(e, i, t.tpe, UNKNOWNGENDER),t.tpe)), Seq.empty[BigInt], UIntType(UnknownWidth))
      case t:BundleType => DoPrim(PrimOps.Cat, t.fields.map(f =>
          hiercat(WSubField(e, f.name, f.tpe, UNKNOWNGENDER), f.tpe)), Seq.empty[BigInt], UIntType(UnknownWidth))
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
      case (mt:VectorType, dt:VectorType) => DoPrim(PrimOps.Cat, (0 to mt.size).map(i =>
          hiermask(WSubIndex(e, i, mt.tpe, UNKNOWNGENDER), mt.tpe, dt.tpe)), Seq.empty[BigInt], UIntType(UnknownWidth))
      case (mt:BundleType, dt:BundleType) => DoPrim(PrimOps.Cat, (mt.fields zip dt.fields).map{ case (mf,df) =>
        hiermask(WSubField(e, mf.name, mf.tpe, UNKNOWNGENDER), mf.tpe, df.tpe) }, Seq.empty[BigInt], UIntType(UnknownWidth))
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
      case ex: WRef => getPart(ex, ex.tpe, rhs, 0)
      case ex: WSubField => getPart(ex, ex.tpe, rhs, 0)
      case ex: WSubIndex => getPart(ex, ex.tpe, rhs, 0)
      case t => error("Invalid LHS expression for fromBits!")
    }
    Block(fbits._2)
  }
  def getPartGround(lhs: Expression, lhst: Type, rhs: Expression, offset: BigInt): (BigInt, Seq[Statement]) = {
    val intWidth = bitWidth(lhst)
    val sel = DoPrim(PrimOps.Bits, Seq(rhs), Seq(offset+intWidth-1,offset), UnknownType)
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
      case t:UIntType => getPartGround(lhs, t, rhs, offset)
      case t:SIntType => getPartGround(lhs, t, rhs, offset)
      case t => error("Unknown type encountered in fromBits!")
    }
  }
}

object MemPortUtils {
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
