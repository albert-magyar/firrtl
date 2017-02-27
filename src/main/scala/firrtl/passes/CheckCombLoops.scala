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

  class CombLoopException(info: Info, mname: String, cycle: List[LogicNode]) extends PassException(
    s"$info: [module $mname] Combinational loop detected: " + cycle.mkString("\n"))

  private def makeMultiMap[K,V] = new mutable.HashMap[K, mutable.Set[V]] with mutable.MultiMap[K,V]

  private case class LogicNode(name: String, inst: Option[String] = None, memport: Option[String] = None)

  // Dependency edges go from dependent to source
  private class DepGraph[T] (
    val vertices: Set[T] = new HashSet[T],
    val edges: Map[T, Set[T]] = new HashMap[T, HashSet[T]]) {
    
    def getVertices = vertices
    def getEdges(v: T) = edges.getOrElse(v, new HashSet[T])

    // Graph must be acyclic for valid linearization
    def linearize(root: T) = {
      val order = new mutable.ArrayBuffer[T]
      val visited = new mutable.HashSet[T]
      def explore(v: T): Unit = {
        visited += v
        for (u  <- getEdges(v)) {
          if (!visited.contains(u)) {
            explore(u)
          }
        }
        order.append(v)
      }
      explore(root)
      order.reverse.toList
    }

    def doBFS(root: T) = {
      val prev = new mutable.HashMap[T,T]
      val queue = new mutable.Queue[T]
      queue.enqueue(root)
      while (!queue.isEmpty) {
        val u = queue.dequeue
        for (v <- getEdges(u)) {
          if (!prev.contains(v)) {
            prev(v) = u
            queue.enqueue(v)
          }
        }
      }
      prev
    }

    def reachabilityBFS(root: T) = doBFS(root).keys.toSet

    def path(start: T, end: T) = {
      val nodePath = new mutable.ArrayBuffer[T]
      val prev = doBFS(start)
      nodePath += end
      while (nodePath.last != start) {
        nodePath += prev(nodePath.last)
      }
      nodePath.toList.reverse
    }

    def findCycles = {
      var counter: BigInt = 0
      val stack = new mutable.Stack[T]
      val onstack = new mutable.HashSet[T]
      val indices = new mutable.HashMap[T, BigInt]
      val lowlinks = new mutable.HashMap[T, BigInt]
      val nonTrivialSCCs = new mutable.ArrayBuffer[List[T]]

      def strongConnect(v: T): Unit = {
        indices(v) = counter
        lowlinks(v) = counter
        counter = counter + 1
        stack.push(v)
        onstack += v
        for (w <- getEdges(v)) {
          if (!indices.contains(w)) {
            strongConnect(w)
            lowlinks(v) = lowlinks(v).min(lowlinks(w))
          } else if (onstack.contains(w)) {
            lowlinks(v) = lowlinks(v).min(indices(w))
          }
        }
        if (lowlinks(v) == indices(v)) {
          val scc = new mutable.ArrayBuffer[T]
          do {
            val w = stack.pop
            onstack -= w
            scc += w } while (scc.last != v)
          if (scc.length > 1) {
            nonTrivialSCCs.append(scc.toList)
          }
        }
      }

      for (v <- vertices) {
        strongConnect(v)
      }

      nonTrivialSCCs.toList
    }



    def simplify(vprime: Set[T]) = {
      val eprime = vprime.map( v => (v,reachabilityBFS(v) & vprime) ).toMap
      new DepGraph(vprime.toSet, eprime)
    }

    def transformNodes(f: (T) => T) = {
      val vprime = vertices.map(f)
      val eprime = edges.map({ case (k,v) => (f(k),v.map(f(_))) })
      new DepGraph(vprime,eprime)
    }

  }

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
    simplifiedModules: mutable.HashMap[String,DepGraph[LogicNode]],
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
    simplifiedModules: mutable.HashMap[String,DepGraph[LogicNode]],
    m: DefModule): DepGraph[LogicNode] = {
    val vertices = new mutable.HashSet[LogicNode]
    val edges = makeMultiMap[LogicNode,LogicNode]
    vertices ++= m.ports map { p => LogicNode(p.name) }
    m map getStmtDeps(simplifiedModules, vertices, edges)
    new DepGraph(vertices.toSet, 
      (edges mapValues { _.toSet }).toMap[LogicNode, Set[LogicNode]])
  }

  private def reportCycle(e: Errors, m: DefModule, moduleGraphs: mutable.HashMap[String,DepGraph[LogicNode]], moduleDeps: mutable.HashMap[String, mutable.HashMap[String,String]])(cycle: List[LogicNode]) = {
    e.append(new CombLoopException(m.info,m.name,cycle))
  }

  def run(c: Circuit): Circuit = {

    val errors = new Errors()

    val moduleMap = c.modules.map({m => (m.name,m) }).toMap
    val moduleDeps = new mutable.HashMap[String, mutable.HashMap[String,String]]
    c.modules.map( m => m map getInstanceGraph(moduleDeps.getOrElseUpdate(m.name, new mutable.HashMap[String,String])) )
    val moduleDepGraph = new DepGraph(moduleMap.keys.toSet,
      (moduleDeps mapValues { _.values.toSet }).toMap[String, Set[String]])
    val topoSortedModules = moduleDepGraph.linearize(c.main).reverse map {moduleMap(_)}
    val moduleGraphs = new mutable.HashMap[String,DepGraph[LogicNode]]
    val simplifiedModules = new mutable.HashMap[String,DepGraph[LogicNode]]
    for (m <- topoSortedModules) {
      val internalDeps = getInternalDeps(simplifiedModules,m)
      val cycles = internalDeps.findCycles
      cycles map reportCycle(errors,m,moduleGraphs,moduleDeps)
      moduleGraphs(m.name) = internalDeps
      simplifiedModules(m.name) = internalDeps.simplify((m.ports map { p => LogicNode(p.name) }).toSet)
    }
    errors.trigger()

    c
  }

}
