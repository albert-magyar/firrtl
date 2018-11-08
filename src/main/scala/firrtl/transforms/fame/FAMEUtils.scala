// See LICENSE for license details.

package firrtl.transforms.fame

import firrtl._
import ir._
import Utils._
import annotations._
import graph.DiGraph
import scala.collection
import collection.mutable.{LinkedHashSet, LinkedHashMap}

abstract class FAMEChannelType

case object WireChannel extends FAMEChannelType

private[fame] class ReferenceTargetRenamer(renames: RenameMap) {
  // TODO: determine order for multiple renames, or just check of == 1 rename?
  def apply(rt: ReferenceTarget): Seq[ReferenceTarget] = {
    renames.get(rt).toSeq.collect({ case rt: ReferenceTarget => rt })
  }
}

case class FAMEChannelAnnotation(name: String, channelType: FAMEChannelType, sources: Option[Seq[ReferenceTarget]], sinks: Option[Seq[ReferenceTarget]]) extends Annotation {
  def update(renames: RenameMap): Seq[Annotation] = {
    val renamer = new ReferenceTargetRenamer(renames)(_)
    Seq(this.copy(sources = sources.map(_ flatMap renamer), sinks = sinks.map(_ flatMap renamer)))
  }
  override def getTargets: Seq[ReferenceTarget] = sources.toSeq.flatten ++ sinks.toSeq.flatten
}

case class TransformedFAMEChannelAnnotation(name: String, channelType: FAMEChannelType, source: Option[ReferenceTarget], sink: Option[ReferenceTarget]) extends Annotation {
  def update(renames: RenameMap): Seq[Annotation] = {
    val renamer = new ReferenceTargetRenamer(renames)(_)
    Seq(this.copy(source = source.flatMap(s => renamer(s).headOption), sink = sink.flatMap(s => renamer(s).headOption)))
  }
  override def getTargets: Seq[ReferenceTarget] = source.toSeq ++ sink.toSeq
}

case class FAME1TransformAnnotation(target: ModuleTarget) extends SingleTargetAnnotation[ModuleTarget] {
  def targets = Seq(target)
  def duplicate(n: ModuleTarget) = this.copy(n)
}

trait Channel {
  def name: String
  def direction: Direction
  def ports: collection.Set[Port]
  def removeCommonPrefix(a: String, b: String): (String, String) = (a, b) match {
    case (a, b) if (a.length == 0 || b.length == 0) => (a, b)
    case (a, b) if (a.charAt(0) == b.charAt(0)) => removeCommonPrefix(a.drop(1), b.drop(1))
    case (a, b) => (a, b)
  }

  def tpe: Type = {
    val fields = ports.map(p => Field(removeCommonPrefix(p.name, name)._1, Default, p.tpe))
    if (fields.size > 1) {
      Decouple(new BundleType(fields.toSeq))
    } else {
      Decouple(fields.head.tpe)
    }
  }
  def asPort: Port = {
    Port(NoInfo, name, direction, tpe)
  }
  def isReady: Expression = WSubField(WRef(name, tpe, PortKind), "ready", Utils.BoolType)
  def isValid: Expression = WSubField(WRef(name, tpe, PortKind), "valid", Utils.BoolType)
  def isFiring: Expression = Reduce.and(Seq(isReady, isValid))
  def replacePortRef(wr: WRef): WSubField = {
    if (ports.size > 1) {
      WSubField(WSubField(WRef(asPort), "bits"), removeCommonPrefix(wr.name, name)._1)
    } else {
      WSubField(WRef(asPort), "bits")
    }
  }
}

case class InputChannel(val name: String, val ports: collection.Set[Port]) extends Channel {
  val direction = Input
  def genTokenLogic(finishing: WRef): Seq[Statement] = {
    Seq(Connect(NoInfo, isReady, finishing))
  }
}

case class OutputChannel(val name: String, val ports: collection.Set[Port], val firedReg: DefRegister) extends Channel {
  val direction = Output
  val isFired = WRef(firedReg)
  val isFiredOrFiring = Reduce.or(Seq(isFired, isFiring))
  def genTokenLogic(finishing: WRef, ccDeps: Iterable[InputChannel]): Seq[Statement] = {
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

object Decouple {
  def apply(t: Type): Type = BundleType(Seq(
    Field("ready", Flip, Utils.BoolType),
    Field("valid", Default, Utils.BoolType),
    Field("bits", Default, t)))
  def apply(p: Port): Port = p.copy(tpe = apply(p.tpe))
}

object IsDecoupled {
  def apply(t: BundleType): Boolean = {
    val sortedFields = t.fields.sortBy(_.name)
    val tailPattern = Seq(
      Field("ready", Utils.swap(sortedFields.head.flip), Utils.BoolType),
      Field("valid", sortedFields.head.flip, Utils.BoolType))
    sortedFields.head.name == "bits" && sortedFields.tail == tailPattern
  }
  def apply(t: Type): Boolean = t match {
    case bt: BundleType => apply(bt)
    case _ => false
  }
}

object Negate {
  def apply(arg: Expression): Expression = DoPrim(PrimOps.Not, Seq(arg), Seq.empty, arg.tpe)
}

object Reduce {
  private def _reduce(op: PrimOp, args: Iterable[Expression]): Expression = {
    args.tail.foldLeft(args.head){ (l, r) => DoPrim(op, Seq(l, r), Seq.empty, UIntType(IntWidth(1))) }
  }
  def and(args: Iterable[Expression]): Expression = _reduce(PrimOps.And, args)
  def or(args: Iterable[Expression]): Expression = _reduce(PrimOps.Or, args)
}

object ChannelCCDependencyGraph {
  def apply(m: Module): LinkedHashMap[OutputChannel, LinkedHashSet[InputChannel]] = {
    new LinkedHashMap[OutputChannel, LinkedHashSet[InputChannel]]
  }
}

