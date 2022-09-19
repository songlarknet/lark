package lack.source

import lack.meta.source.compound.{given, _}
import lack.meta.source.compound.implicits._
import lack.meta.source.stream.{Stream, SortRepr, Bool, Int32}
import lack.meta.source.stream
import lack.meta.source.node.{Builder, Node, NodeInvocation}
import lack.meta.driver.check

object TestBounds:

  def main(args: Array[String]): Unit =
    check.success() { new LemmaBounds(3, _) }

  class LemmaBounds(n: Int, invocation: NodeInvocation) extends Node(invocation):
    val human  = local[Int32]
    val OVERRIDE    = i32(100)


    val human_in_bounds = human < OVERRIDE
    val last_in_bounds  = LastN(n, human_in_bounds)
    val mean            = MeanN(n, human)
    val mean_in_bounds  = mean < OVERRIDE
    val prop            = last_in_bounds ==> mean_in_bounds

    check("if last_in_bounds then mean_in_bounds") {
      prop
    }

    def LastN(n: Int, e: Stream[Bool]): Stream[Bool] = n match
      case 0 => True
      case 1 => e
      case _ => e && LastN(n - 1, fby(False, e))

    def MeanN(n: Int, v: Stream[Int32]): Stream[Int32] =
      SumN(n, v) / n

    def SumN(n: Int, v: Stream[Int32]): Stream[Int32] = n match
      case 0 => 0
      case 1 => v
      case _ => v + SumN(n - 1, fby(i32(0), v))


  // class Surplus(n: Int, invocation: NodeInvocation) extends Node(invocation):
  //   def MeanN(n: Int, v: Stream[Int32]): Stream[Int32] =
  //     SumN(n, v) / n

  //   def SumN(n: Int, v: Stream[Int32]): Stream[Int32] = n match
  //     case 0 => 0
  //     case 1 => v
  //     case _ => v + SumN(n - 1, fby(0, v))

  //   def LastN(n: Int, e: Stream[Bool]): Stream[Bool] = n match
  //     case 0 => True
  //     case 1 => e
  //     case _ => e && LastN(n - 1, fby(False, e))

  //   val OVERRIDE = 100
  //   val HISTORY  = 2

  //   def SteerSelector(human: Stream[Int32], machine: Stream[Int32]): Stream[Int32] =
  //     val human_filtered = MeanN(HISTORY, human)
  //     cond(
  //       when(human_filtered >= OVERRIDE) { human },
  //       otherwise { machine })

  //   val human = i32(1)
  //   val machine = i32(1)
  //   check("if no human override then machine control") {
  //     LastN(HISTORY, human < OVERRIDE) ==> (SteerSelector(human, machine) == machine)
  //   }
  //   check("if no human override then machine control") {
  //     LastN(HISTORY, human < OVERRIDE) ==> MeanN(HISTORY, human) < OVERRIDE
  //   }

  //   check("if no human override then machine control") {
  //     human < OVERRIDE && fby(False, human < OVERRIDE) ==>
  //       ((human + fby(0, human)) / 2 < OVERRIDE)
  //   }

  //   check("bounds-2: if no human override then machine control") {
  //     val human_in_bounds = human < OVERRIDE
  //     val last_fby        = fby(False, human_in_bounds)
  //     val last_in_bounds  = human_in_bounds && last_fby

  //     val mean_fby        = fby(i32(0), human)
  //     val mean_sum        = human + mean_fby
  //     val mean            = mean_sum / 2
  //     val mean_in_bounds  = mean < OVERRIDE

  //     last_in_bounds ==> mean_in_bounds
  //   }

  //   check("bounds-3: if no human override then machine control") {
  //     val human_in_bounds = human < OVERRIDE
  //     val last_fby1       = fby(False, human_in_bounds)
  //     val last_fby2       = fby(False, last_fby1)
  //     val last_in_bounds  = human_in_bounds && last_fby1 && last_fby2
  //     val mean_fby1       = fby(i32(0), human)
  //     val mean_fby2       = fby(i32(0), mean_fby1)
  //     val mean_sum        = human + mean_fby1 + mean_fby2
  //     val mean            = mean_sum / 3
  //     val mean_in_bounds  = mean < OVERRIDE

  //     last_in_bounds ==> mean_in_bounds
  //   }
