// See LICENSE for license details.

package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import scala.collection.mutable
import scala.collection.immutable.HashSet
import scala.collection.immutable.HashMap
import annotation.tailrec

object CheckCombLoops extends Pass {
  def name = "Check Loops"

  class CombLoopException(info: Info, mname: String, cycle: List[String]) extends PassException(
    s"$info: [module $mname] Combinational loop detected:\n" + cycle.mkString("\n"))

  private def makeMultiMap[K,V] = new mutable.HashMap[K, mutable.Set[V]] with mutable.MultiMap[K,V]

  private case class LogicNode(name: String, inst: Option[String] = None, memport: Option[String] = None)

  // Dependency edges go from dependent to source

  private def getInstanceGraph(deps: mutable.HashMap[String,String])(s: Statement): Statement = s match {
    case i: WDefInstance =>
      deps(i.name) = i.module
      i
    case _ =>
      s map getInstanceGraph(deps)
      s
  }

  private def toLogicNode(e: Expression): LogicNode = e match {
    case r: WRef =>
      LogicNode(r.name)
    case s: WSubField =>
      s.exp match {
        case modref: WRef =>
          LogicNode(s.name,Some(modref.name))
        case memport: WSubField =>
          memport.exp match {
            case memref: WRef =>
              LogicNode(s.name,Some(memref.name),Some(memport.name))
          }
      }
  }

  private def getExprDeps(deps: mutable.Set[LogicNode])(e: Expression): Expression = e match {
    case r: WRef =>
      deps += toLogicNode(r)
      r
    case s: WSubField =>
      deps += toLogicNode(s)
      s
    case _ =>
      e map getExprDeps(deps)
      e
  }

  private def getStmtDeps(
    simplifiedModules: mutable.HashMap[String,DiGraph[LogicNode]],
    nodes: mutable.Set[LogicNode],
    deps: mutable.MultiMap[LogicNode,LogicNode])(s: Statement): Statement = s match {
    case c: Connect =>
      val lhs = toLogicNode(c.loc)
      if (nodes.contains(lhs)) {
        getExprDeps(deps.getOrElseUpdate(lhs,new mutable.HashSet[LogicNode]))(c.expr)
      }
      c
    case w: DefWire =>
      nodes += LogicNode(w.name)
      w
    case n: DefNode =>
      val lhs = LogicNode(n.name)
      nodes += lhs
      getExprDeps(deps.getOrElseUpdate(lhs,new mutable.HashSet[LogicNode]))(n.value)
      n
    case m: DefMemory =>
      if (m.readLatency == 0) {
        for (rp <- m.readers) {
          val dataNode = LogicNode("data",Some(m.name),Some(rp))
          val addrNode = LogicNode("addr",Some(m.name),Some(rp))
          val enNode = LogicNode("en",Some(m.name),Some(rp))
          nodes ++= Seq(dataNode,addrNode,enNode)
          deps(dataNode) = new mutable.HashSet[LogicNode]
          deps(dataNode) ++= Seq(addrNode,enNode)
        }
      }
      m
    case i: WDefInstance =>
      val iGraph = simplifiedModules(i.module).transformNodes(n => n.copy(inst = Some(i.name)))
      nodes ++= iGraph.vertices
      deps ++= iGraph.edges.map({ case (k, v) => (k, mutable.HashSet(v.toList:_*)) }).toList
      i
    case _ =>
      s map getStmtDeps(simplifiedModules,nodes,deps)
      s
  }

  private def getInternalDeps(
    simplifiedModules: mutable.HashMap[String,DiGraph[LogicNode]],
    m: DefModule): DiGraph[LogicNode] = {
    val vertices = new mutable.HashSet[LogicNode]
    val edges = makeMultiMap[LogicNode,LogicNode]
    vertices ++= m.ports map { p => LogicNode(p.name) }
    m map getStmtDeps(simplifiedModules, vertices, edges)
    new DiGraph(vertices.toSet, 
      (edges mapValues { _.toSet }).toMap[LogicNode, Set[LogicNode]])
  }

  private def recoverCycle(m: String, moduleGraphs: mutable.HashMap[String,DiGraph[LogicNode]], moduleDeps: mutable.HashMap[String, mutable.HashMap[String,String]], prefix: String, cycle: List[LogicNode]): List[String] = {
    val cycNodes = (cycle zip cycle.tail) map { case (a, b) =>
      if (a.inst.isDefined && !a.memport.isDefined && a.inst == b.inst) {
        val child = moduleDeps(m)(a.inst.get)
        val newprefix = prefix + a.inst.get + "."
        recoverCycle(child,moduleGraphs,moduleDeps,newprefix,moduleGraphs(child).path(b.copy(inst=None),a.copy(inst=None)).tail.reverse)
      } else {
        List(prefix + a.name.toString)
      }
    }
    cycNodes.flatten ++ List(prefix + cycle.last.name.toString)
  }

/*
  private class ModuleLoopChecker(m: DefModule, otherModules: Map[String,ModuleLoopChecker]) {
    val name = m.name
    // map instname -> moduledata
    val children = ...
    val nodes = empty set
    val deps = empty map
    getInstanceGraph(
 */

  def run(c: Circuit): Circuit = {

    val errors = new Errors()

    val moduleMap = c.modules.map({m => (m.name,m) }).toMap
    val moduleDeps = new mutable.HashMap[String, mutable.HashMap[String,String]]
    c.modules.map( m => m map getInstanceGraph(moduleDeps.getOrElseUpdate(m.name, new mutable.HashMap[String,String])) )
    val moduleDiGraph = new DiGraph(moduleMap.keys.toSet,
      (moduleDeps mapValues { _.values.toSet }).toMap[String, Set[String]])
    val topoSortedModules = moduleDiGraph.linearize(c.main).reverse map {moduleMap(_)}
    val moduleGraphs = new mutable.HashMap[String,DiGraph[LogicNode]]
    val simplifiedModules = new mutable.HashMap[String,DiGraph[LogicNode]]
    for (m <- topoSortedModules) {
      val internalDeps = getInternalDeps(simplifiedModules,m)
      val cycles = internalDeps.findCycles
      cycles map (c => errors.append(new CombLoopException(m.info, m.name, recoverCycle(m.name,moduleGraphs,moduleDeps,m.name + ".",c))))
      moduleGraphs(m.name) = internalDeps
      simplifiedModules(m.name) = internalDeps.simplify((m.ports map { p => LogicNode(p.name) }).toSet)
    }
    errors.trigger()

    c
  }

}
