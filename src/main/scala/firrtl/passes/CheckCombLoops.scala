// See LICENSE for license details.

package firrtl.passes

import scala.collection.mutable
import scala.collection.immutable.HashSet
import scala.collection.immutable.HashMap
import annotation.tailrec

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.analyses.InstanceGraph

object CheckCombLoops extends Pass {
  def name = "Check Loops"

  class CombLoopException(info: Info, mname: String, cycle: List[String]) extends PassException(
    s"$info: [module $mname] Combinational loop detected:\n" + cycle.mkString("\n"))

  private case class LogicNode(name: String, inst: Option[String] = None, memport: Option[String] = None)

  // Dependency edges go from dependent to source


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
    deps: MutableDiGraph[LogicNode])(s: Statement): Statement = s match {
    case c: Connect =>
      val lhs = toLogicNode(c.loc)
      if (deps.contains(lhs)) {
        getExprDeps(deps.getEdges(lhs))(c.expr)
      }
      c
    case w: DefWire =>
      deps.addVertex(LogicNode(w.name))
      w
    case n: DefNode =>
      val lhs = LogicNode(n.name)
      deps.addVertex(lhs)
      getExprDeps(deps.getEdges(lhs))(n.value)
      n
    case m: DefMemory if (m.readLatency == 0) =>
      for (rp <- m.readers) {
        val dataNode = deps.addVertex(LogicNode("data",Some(m.name),Some(rp)))
        deps.addEdge(dataNode, deps.addVertex(LogicNode("addr",Some(m.name),Some(rp))))
        deps.addEdge(dataNode, deps.addVertex(LogicNode("en",Some(m.name),Some(rp))))
      }
      m
    case i: WDefInstance =>
      val iGraph = simplifiedModules(i.module).transformNodes(n => n.copy(inst = Some(i.name)))
      for (v <- iGraph.getVertices) {
        deps.addVertex(v)
        iGraph.getEdges(v).foreach { deps.addEdge(v,_) }
      }
      i
    case _ =>
      s map getStmtDeps(simplifiedModules,deps)
      s
  }

  private def getInternalDeps(
    simplifiedModules: mutable.HashMap[String,DiGraph[LogicNode]],
    m: DefModule): DiGraph[LogicNode] = {
    val deps = new MutableDiGraph[LogicNode]
    m.ports foreach { p => deps.addVertex(LogicNode(p.name)) }
    m map getStmtDeps(simplifiedModules, deps)
    DiGraph(deps)
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

  private def getInstanceGraph(deps: mutable.HashMap[String,String])(s: Statement): Statement = s match {
    case i: WDefInstance =>
      deps(i.name) = i.module
      i
    case _ =>
      s map getInstanceGraph(deps)
      s
  }

  def run(c: Circuit): Circuit = {

    val errors = new Errors()

    val moduleMap = c.modules.map({m => (m.name,m) }).toMap
    val iGraph = new InstanceGraph(c)
    val moduleDeps = new mutable.HashMap[String, mutable.HashMap[String,String]]
    c.modules.map( m => m map getInstanceGraph(moduleDeps.getOrElseUpdate(m.name, new mutable.HashMap[String,String])) )
    val topoSortedModules = iGraph.graph.transformNodes(_.module).linearize(c.main).reverse map { moduleMap(_) }
    val moduleGraphs = new mutable.HashMap[String,DiGraph[LogicNode]]
    val simplifiedModules = new mutable.HashMap[String,DiGraph[LogicNode]]
    for (m <- topoSortedModules) {
      val internalDeps = getInternalDeps(simplifiedModules,m)
      val cycles = internalDeps.findCycles
      cycles map (c => errors.append(new CombLoopException(m.info, m.name, recoverCycle(m.name,moduleGraphs,moduleDeps
,m.name + ".",c))))
      moduleGraphs(m.name) = internalDeps
      simplifiedModules(m.name) = internalDeps.simplify((m.ports map { p => LogicNode(p.name) }).toSet)
    }
    errors.trigger()

    c
  }

}
