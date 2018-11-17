// See LICENSE for license details.

package firrtl.transforms.fame

import firrtl._
import ir._
import Utils._
import Mappers._
import annotations._
import graph.DiGraph
import scala.collection
import collection.mutable
import collection.mutable.{LinkedHashSet, LinkedHashMap, MultiMap}

abstract class FAMEChannelType
case object WireChannel extends FAMEChannelType
case class FAMEChannelAnnotation(name: String, channelType: FAMEChannelType, sources: Option[Seq[ReferenceTarget]], sinks: Option[Seq[ReferenceTarget]]) extends Annotation {
  def update(renames: RenameMap): Seq[Annotation] = {
    val renamer = new ReferenceTargetRenamer(renames)(_)
    Seq(this.copy(sources = sources.map(_ flatMap renamer), sinks = sinks.map(_ flatMap renamer)))
  }
  override def getTargets: Seq[ReferenceTarget] = sources.toSeq.flatten ++ sinks.toSeq.flatten
}

abstract class FAMETransformType
case object FAME1Transform extends FAMETransformType
case class FAMETransformAnnotation(transformType: FAMETransformType, target: ModuleTarget) extends SingleTargetAnnotation[ModuleTarget] {
  def targets = Seq(target)
  def duplicate(n: ModuleTarget) = this.copy(transformType, n)
}

private[fame] class ReferenceTargetRenamer(renames: RenameMap) {
  // TODO: determine order for multiple renames, or just check of == 1 rename?
  def apply(rt: ReferenceTarget): Seq[ReferenceTarget] = {
    renames.get(rt).getOrElse(Seq(rt)).collect({ case rt: ReferenceTarget => rt })
  }
}

private[fame] object FAMEChannelAnalysis {
  def removeCommonPrefix(a: String, b: String): (String, String) = (a, b) match {
    case (a, b) if (a.length == 0 || b.length == 0) => (a, b)
    case (a, b) if (a.charAt(0) == b.charAt(0)) => removeCommonPrefix(a.drop(1), b.drop(1))
    case (a, b) => (a, b)
  }

  def getChannelType(name: String, ports: Seq[Port]): Type = {
    val fields = ports.map(p => Field(removeCommonPrefix(p.name, name)._1, Default, p.tpe))
    if (fields.size > 1) {
      Decouple(new BundleType(fields.toSeq))
    } else {
      Decouple(fields.head.tpe)
    }
  }

}

private[fame] class FAMEChannelAnalysis(val state: CircuitState, val fameType: FAMETransformType) {
  // TODO: only transform submodules of model modules
  // TODO: add renames!
  val circuit = state.circuit
  val syncModules = circuit.modules.filter(_.ports.exists(_.tpe == ClockType)).map(m => ModuleTarget(circuit.main, m.name)).toSet
  val moduleNodes = new LinkedHashMap[ModuleTarget, DefModule]
  val portNodes = new LinkedHashMap[ReferenceTarget, Port]
  circuit.modules.foreach({
    m => {
      val mTarget = ModuleTarget(circuit.main, m.name)
      moduleNodes(mTarget) = m
      m.ports.foreach({
        p => portNodes(mTarget.ref(p.name)) = p
      })
    }
  })

  val transformedModules = new LinkedHashSet[ModuleTarget]
  state.annotations.collect({
    case fta @ FAMETransformAnnotation(tpe, mt) if (tpe == fameType) =>
      transformedModules += mt
  })

  val channels = new LinkedHashSet[String]
  val transformedSinks = new LinkedHashSet[String]
  val transformedSources = new LinkedHashSet[String]
  val sinkModel = new LinkedHashMap[String, ModuleTarget]
  val sourceModel = new LinkedHashMap[String, ModuleTarget]
  val sinkPorts = new LinkedHashMap[String, Seq[ReferenceTarget]]
  val sourcePorts = new LinkedHashMap[String, Seq[ReferenceTarget]]
  val staleTopPorts = new LinkedHashSet[ReferenceTarget]
  state.annotations.collect({
    case fca: FAMEChannelAnnotation =>
      channels += fca.name
      val sinks = fca.sinks.toSeq.flatten
      sinkPorts(fca.name) = sinks
      sinks.headOption.filter(rt => transformedModules.contains(ModuleTarget(rt.circuit, rt.encapsulatingModule))).foreach({ rt =>
        sinkModel(fca.name) = ModuleTarget(rt.circuit, rt.module)
        transformedSinks += fca.name
        staleTopPorts ++= sinks
      })
      val sources = fca.sources.toSeq.flatten
      sourcePorts(fca.name) = sources
      sources.headOption.filter(rt=> transformedModules.contains(ModuleTarget(rt.circuit, rt.encapsulatingModule))).foreach({ rt =>
        sourceModel(fca.name) = ModuleTarget(rt.circuit, rt.module)
        transformedSources += fca.name
        staleTopPorts ++= sources
      })
  })

  val topTarget = ModuleTarget(circuit.main, circuit.main)
  private val moduleOf = new LinkedHashMap[String, String]
  val topConnects = new LinkedHashMap[ReferenceTarget, ReferenceTarget]
  val inputChannels = new LinkedHashMap[ModuleTarget, mutable.Set[String]] with MultiMap[ModuleTarget, String]
  val outputChannels = new LinkedHashMap[ModuleTarget, mutable.Set[String]] with MultiMap[ModuleTarget, String]
  moduleNodes(topTarget).asInstanceOf[Module].body.map(getTopConnects)
  def getTopConnects(stmt: Statement): Statement = stmt.map(getTopConnects) match {
    case WDefInstance(_, iname, mname, _) =>
      moduleOf(iname) = mname
      EmptyStmt
    case Connect(_, WRef(cname, _, _, _), WSubField(WRef(iname, _, _, _), pname, _, _)) =>
      val child = ModuleTarget(circuit.main, moduleOf(iname))
      topConnects(topTarget.ref(cname)) = child.ref(pname)
      outputChannels.addBinding(child, cname)
      EmptyStmt
    case Connect(_, WSubField(WRef(iname, _, _, _), pname, _, _), WRef(cname, _, _, _)) =>
      val child = ModuleTarget(circuit.main, moduleOf(iname))
      topConnects(topTarget.ref(cname)) = child.ref(pname)
      inputChannels.addBinding(child, cname)
      EmptyStmt
    case s => EmptyStmt
  }
  // TODO: call getTopConnects
  def inputPortsByChannel(m: DefModule): Map[String, Seq[Port]] = {
    val iChannels = inputChannels.get(ModuleTarget(circuit.main, m.name)).toSet.flatten
    iChannels.map({
      cname => (cname, sinkPorts(cname).map(topConnects(_)).map(portNodes(_)))
    }).toMap
  }

  def outputPortsByChannel(m: DefModule): Map[String, Seq[Port]] = {
    val oChannels = outputChannels.get(ModuleTarget(circuit.main, m.name)).toSet.flatten
    oChannels.map({
      cname => (cname, sourcePorts(cname).map(topConnects(_)).map(portNodes(_)))
    }).toMap
  }

  def getSinkChannelType(cName: String): Type = {
    FAMEChannelAnalysis.getChannelType(cName, sinkPorts(cName).map(portNodes(_)))
  }

  def getSourceChannelType(cName: String): Type = {
    FAMEChannelAnalysis.getChannelType(cName, sourcePorts(cName).map(portNodes(_)))
  }
}


