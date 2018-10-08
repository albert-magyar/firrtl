// See LICENSE for license details.

package firrtl.transforms.fame

import firrtl._
import ir._
import Utils._
import annotations._
import graph.DiGraph
import scala.collection
import collection.mutable.{LinkedHashSet, LinkedHashMap}

trait Channel {
  def name: String
  def direction: Direction
  def ports: collection.Set[Port]
  def tpe: Type = {
    val fields = ports.map(p => Field(p.name, Default, p.tpe))
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
      WSubField(WSubField(WRef(asPort), "bits"), wr.name)
    } else {
      WSubField(WRef(asPort), "bits")
    }
  }
}

case class InputChannel(val name: String, val ports: collection.Set[Port]) extends Channel {
  val direction = Input
  def genTokenLogic(finishing: DefWire): Seq[Statement] = {
    Seq(Connect(NoInfo, isReady, WRef(finishing)))
  }
}

case class OutputChannel(val name: String, val ports: collection.Set[Port], val firedReg: DefRegister) extends Channel {
  val direction = Output
  val isFired = WRef(firedReg)
  val isFiredOrFiring = Reduce.or(Seq(isFired, isFiring))
  def genTokenLogic(finishing: DefWire, ccDeps: Iterable[InputChannel]): Seq[Statement] = {
    val regUpdate = Connect(
      NoInfo,
      isFired,
      Mux(WRef(finishing),
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

object FAMEAnnotate {
  def apply(c: Circuit, m: Module): FAMETransformAnnotation = {
    FAMETransformAnnotation(ModuleName(m.name, CircuitName(c.main)), m.ports.filter(_.tpe != ClockType).map(p => (p.name, p.name)).toMap)
  }
}

// PortChannel key = port name, value = channel name
case class FAMETransformAnnotation(target: Named, val portChannels: collection.Map[String, String]) extends SingleTargetAnnotation[Named] {
  def bindToModule(m: Module): FAMEPortMap = target match {
    case ModuleName(m.name, _) => new FAMEPortMap(m, portChannels)
    case _ => Utils.throwInternalError(s"FAMETransformAnnotation does not match module $m.name")
  }
  def duplicate(n: Named) = new FAMETransformAnnotation(n, portChannels)
}

class FAMEPortMap(m: Module, portChannels: collection.Map[String, String]) {
  val irPortChannels = m.ports.collect({ case p if portChannels.contains(p.name) => (p, portChannels(p.name)) })

  def getInputChannels(m: Module): LinkedHashMap[String, LinkedHashSet[Port]] = {
    val iChannelPorts = new LinkedHashMap[String, LinkedHashSet[Port]]
    irPortChannels.collect({
      case (port @ Port(_,_,Input,_), cName) =>
        iChannelPorts.getOrElseUpdate(cName, new LinkedHashSet[Port]) += port
    })
    iChannelPorts
  }

  def getOutputChannels(m: Module): LinkedHashMap[String, LinkedHashSet[Port]] = {
    val oChannelPorts = new LinkedHashMap[String, LinkedHashSet[Port]]
    irPortChannels.collect({
      case (port @ Port(_,_,Output,_), cName) =>
        oChannelPorts.getOrElseUpdate(cName, new LinkedHashSet[Port]) += port
    })
    oChannelPorts
  }
}
