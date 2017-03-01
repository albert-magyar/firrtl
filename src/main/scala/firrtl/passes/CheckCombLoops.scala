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
    simplifiedModules: mutable.Map[String,DiGraph[LogicNode]],
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

  private def recoverCycle(m: String, moduleGraphs: mutable.Map[String,DiGraph[LogicNode]], moduleDeps: Map[String, Map[String,String]], prefix: List[String], cycle: List[LogicNode]): List[String] = {
    def absNodeName(prefix: List[String], n: LogicNode) = 
      (prefix ++ n.inst ++ n.memport :+ n.name).mkString(".")
    val cycNodes = (cycle zip cycle.tail) map { case (a, b) =>
      if (a.inst.isDefined && !a.memport.isDefined && a.inst == b.inst) {
        val child = moduleDeps(m)(a.inst.get)
        val newprefix = prefix :+ a.inst.get
        val subpath = moduleGraphs(child).path(b.copy(inst=None),a.copy(inst=None)).tail.reverse
        recoverCycle(child,moduleGraphs,moduleDeps,newprefix,subpath)
      } else {
        List(absNodeName(prefix,a))
      }
    }
    cycNodes.flatten :+ absNodeName(prefix, cycle.last)
  }


  // TODO: deal with exmodules!
  def run(c: Circuit): Circuit = {
    val errors = new Errors()
    val moduleMap = c.modules.map({m => (m.name,m) }).toMap
    val iGraph = new InstanceGraph(c)
    val moduleDeps = iGraph.graph.edges.map{ case (k,v) => (k.module, (v map { i => (i.name, i.module) }).toMap) }
    val topoSortedModules = iGraph.graph.transformNodes(_.module).linearize(c.main).reverse map { moduleMap(_) }
    val moduleGraphs = new mutable.HashMap[String,DiGraph[LogicNode]]
    val simplifiedModuleGraphs = new mutable.HashMap[String,DiGraph[LogicNode]]
    for (m <- topoSortedModules) {
      val internalDeps = new MutableDiGraph[LogicNode]
      m.ports foreach { p => internalDeps.addVertex(LogicNode(p.name)) }
      m map getStmtDeps(simplifiedModuleGraphs, internalDeps)
      moduleGraphs(m.name) = DiGraph(internalDeps)
      simplifiedModuleGraphs(m.name) = moduleGraphs(m.name).simplify((m.ports map { p => LogicNode(p.name) }).toSet)
      for (scc <- moduleGraphs(m.name).findSCCs.filter(_.length > 1)) {
        val cycle = recoverCycle(m.name,moduleGraphs,moduleDeps,List(m.name),scc :+ scc.head)
        errors.append(new CombLoopException(m.info, m.name, cycle))
      }
    }
    errors.trigger()
    c
  }

}
