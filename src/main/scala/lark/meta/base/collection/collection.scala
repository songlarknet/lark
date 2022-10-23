package lark.meta.base

import lark.meta.base.names.given
import lark.meta.base.{names, pretty}

import scala.collection.{SortedMap, SortedSet}
import scala.math.Ordering.Implicits._

package object collection:

  /** Graph with no edge information.
   * Vertices are stored in an (ordered) list so that the topological sort can
   * reuse that order wherever possible.
   */
  case class Graph[T: scala.math.Ordering](
    vertices: List[T],
    edges: MultiMapSet[T, T]
  ):
    /** Find cycles that go through given node. */
    def cycles(to: T): List[List[T]] =
      edges(to).toList.flatMap(cycles(SortedSet(to), _))

    def cycles(seen: SortedSet[T], from: T): List[List[T]] =
      if seen.contains(from)
      then List(List(from))
      else for
        fromX <- edges(from).toList
        fromXX <- cycles(seen + from, fromX)
      yield fromX :: fromXX

    /** Topological sort.
     * Throws except.CycleException if no topological ordering exists. */
    def topsort: List[T] =
      topsortMany(SortedSet.empty, SortedSet.empty, vertices)._1

    def topsortMany(
      emitted: SortedSet[T],
      successors: SortedSet[T],
      entries: List[T]
    ): (List[T], SortedSet[T]) = entries match
      case Nil => (List(), emitted)
      case e :: es =>
        val (l1, e1) = topsortOne(emitted, successors, e)
        val (l2, e2) = topsortMany(e1, successors, es)
        (l1 ++ l2, e2)

    def topsortOne(
      emitted: SortedSet[T],
      successors: SortedSet[T],
      entry: T
    ): (List[T], SortedSet[T]) =
      if successors.contains(entry) then
        throw new except.CycleException(entry)
      else if emitted.contains(entry) then
        (List(), emitted)
      else
        val (l1, e1) = topsortMany(emitted + entry, successors + entry, edges(entry).toList)
        (l1 :+ entry, e1)

    def reverse: Graph[T] =
      val edgesX =
        edges.entries.toList.flatMap { (src,snks) =>
          snks.map { snk =>
            snk -> src
          }
        }
      Graph(vertices,
        MultiMapSet.concat(edgesX.map(MultiMapSet.just)))

  /** Map with duplicate keys, where duplicates are stored as a list. */
  case class MultiMap[K: scala.math.Ordering, V](entries: SortedMap[K, List[V]]):
    def <>(that: MultiMap[K, V]): MultiMap[K, V] =
      MultiMap(
        that.entries.foldLeft(this.entries) { case (acc, (k,v)) =>
          acc + (k -> (acc.getOrElse(k, List.empty[V]) ++ v))
        })

    def apply(key: K): List[V] =
      entries.getOrElse(key, List.empty)

  object MultiMap:
    def apply[K: scala.math.Ordering, V](elems: (K, List[V])*): MultiMap[K, V] =
      val elemsX = elems.map { case (k,v) => MultiMap(SortedMap(k -> v)) }
      concat(elemsX.toSeq)

    def empty[K: scala.math.Ordering, V] =
      MultiMap[K, V](SortedMap.empty[K, List[V]])

    def just[K: scala.math.Ordering, V](key: K, value: V) =
      MultiMap(SortedMap(key -> List(value)))

    def concat[K: scala.math.Ordering, V](maps: Iterable[MultiMap[K, V]]) =
      maps.foldLeft(MultiMap.empty[K, V])(_ <> _)


  /** Map with duplicate keys, where duplicates are stored as a set. */
  case class MultiMapSet[K: scala.math.Ordering, V: scala.math.Ordering](entries: SortedMap[K, SortedSet[V]]):
    def <>(that: MultiMapSet[K, V]): MultiMapSet[K, V] =
      MultiMapSet(
        that.entries.foldLeft(this.entries) { case (acc, (k,v)) =>
          acc + (k -> (acc.getOrElse(k, SortedSet.empty[V]) ++ v))
        })

    def apply(key: K): SortedSet[V] =
      entries.getOrElse(key, SortedSet.empty)

  object MultiMapSet:
    def apply[K: scala.math.Ordering, V: scala.math.Ordering](elems: (K, SortedSet[V])*): MultiMapSet[K, V] =
      val elemsX = elems.map { case (k,v) => MultiMapSet(SortedMap(k -> v)) }
      concat(elemsX)

    def empty[K: scala.math.Ordering, V: scala.math.Ordering] =
      MultiMapSet[K, V](SortedMap.empty[K, SortedSet[V]])

    def just[K: scala.math.Ordering, V: scala.math.Ordering](key: K, value: V) =
      MultiMapSet(SortedMap(key -> SortedSet(value)))

    def concat[K: scala.math.Ordering, V: scala.math.Ordering](maps: Iterable[MultiMapSet[K, V]]) =
      maps.foldLeft(MultiMapSet.empty[K, V])(_ <> _)


  object except:
    class CycleException[T](val value: T) extends Exception(
      s"""Topological sort: cycles.
        | Entries: ${value}
        |""".stripMargin)
