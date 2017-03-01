package firrtl

import scala.collection.immutable.{HashSet, HashMap}
import scala.collection.mutable

class MutableDiGraph[T] {
  val edgeData = new mutable.HashMap[T, mutable.Set[T]] with mutable.MultiMap[T, T]
  def contains(v: T) = edgeData.contains(v)
  def getVertices = edgeData.keys
  def getEdges(v: T) = edgeData(v)
  def addVertex(v: T) = edgeData.getOrElseUpdate(v,new mutable.HashSet[T])
  def addEdge(u: T, v: T) = edgeData.addBinding(u,v)
  def toDiGraph = new DiGraph(edgeData.keys.toSet,
      (edgeData mapValues { _.toSet }).toMap[T, Set[T]])
}


class DiGraph[T] (
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
    new DiGraph(vprime.toSet, eprime)
  }

  def transformNodes[Q](f: (T) => Q): DiGraph[Q] = {
    val vprime = vertices.map(f)
    val eprime = edges.map({ case (k,v) => (f(k),v.map(f(_))) })
    new DiGraph(vprime,eprime)
  }

}
