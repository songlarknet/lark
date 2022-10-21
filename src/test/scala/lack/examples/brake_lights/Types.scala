package lack.examples.brake_lights

import lack.meta.base.num

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.node
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, UInt8, UInt16, Int32, Real}
import lack.meta.macros.Location

object Types:

  /** Data from IMU: accelerometer vector and gyroscope quaternion. */
  case class AccelGyro(clock: Stream[Bool], accel: V3, gyro: V4) extends node.Invocation.Freshen:
    def freshen(name: String, invocation: node.Invocation): AccelGyro =
      AccelGyro(
        invocation.stream(name + "_ck", clock),
        accel.freshen(name + "_accel", invocation),
        gyro.freshen(name + "_gyro", invocation))

  /** 3-dimensional vector of reals */
  case class V3(x: Stream[Real], y: Stream[Real], z: Stream[Real]) extends node.Invocation.Freshen:
    def freshen(name: String, invocation: node.Invocation): V3 =
      V3(
        invocation.stream(name + "_x", x),
        invocation.stream(name + "_y", y),
        invocation.stream(name + "_z", z))

    def ==(that: V3)(using builder: node.Builder, location: Location): Stream[Bool] =
      this.x == that.x && this.y == that.y && this.z == that.z
    def !=(that: V3)(using builder: node.Builder, location: Location): Stream[Bool] =
      !(this == that)

  object V3:
    def apply(value: num.Real): V3 = V3(real(value), real(value), real(value))
    def zero: V3 = V3(0)

  /** Quaternion */
  case class V4(a: Stream[Real], b: Stream[Real], c: Stream[Real], d: Stream[Real]) extends node.Invocation.Freshen:
    def freshen(name: String, invocation: node.Invocation): V4 =
      V4(
        invocation.stream(name + "_a", a),
        invocation.stream(name + "_b", b),
        invocation.stream(name + "_c", c),
        invocation.stream(name + "_d", d))
