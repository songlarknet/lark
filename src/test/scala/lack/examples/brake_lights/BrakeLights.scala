package lack.examples.brake_lights

import lack.meta.base.num
import lack.meta.base.num.Integer

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Automaton
import lack.meta.source.node
import lack.meta.source.Node
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, UInt8, UInt16, Int32, Real}
import lack.meta.driver.{Check, Compile, Grind}
import lack.meta.source.Sneaky

import Types.{V3, V4, AccelGyro}

import scala.concurrent.duration.DurationInt

class BrakeLights extends munit.FunSuite:
  test("Check") {
    Check.success() { BrakeLights.Top(_) }
  }

  test("Compile") {
    Compile.compile(
      basename = "brake_lights",
      output = Some(java.nio.file.Paths.get("scratch/c/")))
      { BrakeLights.Top(_) }
  }

  // Quite slow
  test("Grind") {
    Grind.grind(Grind.Options(count = 10)) { BrakeLights.Top(_) }
  }

/** Accelerometer-based motorcycle brake lights inference.
 * In normal riding conditions, motorcyclists tend to use engine braking before
 * applying the conventional brakes. Unlike conventional brakes,
 * however, applying engine braking will not enable the brake lights. This
 * lack of brake lights means that any vehicles behind the motorcycle are less
 * likely to notice the braking, which could increase accident risk. The goal
 * of braking inference is to infer when engine braking is happening and enable
 * the brake lights automatically.
 *
 * Specifications:
 *  Maximum acceleration of motorcycle: 0-100km/h in 5s  ~ 5.5m/s/s.
 *  Maximum acceleration of motorcycle: 0-180km/h in 14s ~ 3.5m/s/s.
 *  Maximum braking ~8m/s/s.
 *  Maximum speed 180km/h ~ 50m/s.
 *
 *  Coasting with clutch in, flat road, deceleration ~ 1-2km/h/s or 0.5m/s/s
 *  Coasting with engine engaged, flat road, deceleration ~ 5km/h/s or 1.4m/s/s.
 *
 * Version zero, simplest possible algorithm:
 *  * use accelerometer only (no gyro).
 *  * assume gravity component of accelerometer changes slowly: remove with high-pass filter.
 *  * assume device is fixed to bike with +Y pointing forward, braking is always -Y.
 */
object BrakeLights:

  /** Get current accelerometer data, allowing for some dropped packets.
   * Dropped packets are treated by repeating the last good packet.
  */
  case class HoldImu(imu: AccelGyro)(invocation: Node.Invocation) extends Node(invocation):
    val accel_x = output[Real]
    val accel_y = output[Real]
    val accel_z = output[Real]
    val accel   = V3(accel_x, accel_y, accel_z)
    val valid   = output[Bool]

    accel_x := Sample.hold(imu.clock, imu.accel.x, 0)
    accel_y := Sample.hold(imu.clock, imu.accel.y, 0)
    accel_z := Sample.hold(imu.clock, imu.accel.z, 0)

    // The output is valid when the accelerometer value is relatively "fresh".
    // For now, only allow one dropped packet for each received packet.
    valid   := imu.clock || fby(False, imu.clock)

    guarantees("available means current") {
      imu.clock ==> (accel_x == imu.accel.x && accel_y == imu.accel.y && accel_z == imu.accel.z)
    }
    guarantees("available means fresh") {
      imu.clock ==> valid
    }

  /** The accelerometer has gravity. Because gravity doesn't change too much,
   * we can try to remove it with a high-pass filter.
   */
  case class RemoveGravity(imu: AccelGyro)(invocation: Node.Invocation) extends Node(invocation):
    val accel_x = output[Real]
    val accel_y = output[Real]
    val accel_z = output[Real]
    val accel   = V3(accel_x, accel_y, accel_z)
    val valid   = output[Bool]

    // Sample-and-hold dropped packets, then apply high-pass filter
    val hold  = subnode(HoldImu(imu))
    accel_x := Filter.iir(RemoveGravity.filter, hold.accel.x)
    accel_y := Filter.iir(RemoveGravity.filter, hold.accel.y)
    accel_z := Filter.iir(RemoveGravity.filter, hold.accel.z)

    // The filter takes some time to warm up because the cutoff period is quite
    // long. Consider the filter to be valid when we have ten seconds of good
    // values.
    valid   := Sample.lastN(RemoveGravity.decay, hold.valid)

    // CSE would be useful,
    val always_zero =
      Sample.sofar(imu.accel.x == real(0) && imu.accel.y == real(0) && imu.accel.z == real(0))
    guarantees("always zero means always zero") {
      always_zero ==> (accel.x == real(0) && accel.y == real(0) && accel.z == real(0))
    }
    guarantees("always zero means held zero") {
      always_zero ==> (hold.accel.x == real(0) && hold.accel.y == real(0) && hold.accel.z == real(0))
    }
    check("sneaky invariant: always zero means all delays are zeros") {
      val iir = Sneaky(this.builder).subnodes("IIR")
      always_zero ==>
      Sneaky.forall(iir) { i =>
        Sneaky.forall(i.variables[Real]("z")) { z => z == 0 }
      }
    }
  object RemoveGravity:
    /** High-pass filter with cut-off frequency of 0.1Hz, or period of 10s. */
    val filter = Filter.Butterworth.hpf_order3_cutoff1em3
    /** Decay of impulse response of filter. 10 seconds. (This should be computed.) */
    val decay  = Sample.Ticks(10.seconds)

  /** Lights controller takes accelerometer and returns true if lights are on */
  case class Lights(accel: V3)(invocation: Node.Invocation) extends Automaton(invocation):
    val light         = output[Bool]

    val braking       = accel.y <= real(Lights.braking)
    val trigger_on    = Sample.lastN(Lights.on,    braking)
    val trigger_off   = Sample.lastN(Lights.off,  !braking)

    check("never on and off") {
      !(trigger_on && trigger_off)
    }

    initial(OFF)
    object OFF extends State:
      unless {
        resume(trigger_on, ON)
      }
      light     := False
    object ON extends State:
      unless {
        resume(trigger_off, OFF)
      }
      light     := True

  object Lights:
    /** Accelerometer measurement at which we are considered to be "braking".
     * This is 1m/s/s, chosen to sit somewhere between the observed engine braking
     * deceleration of ~1.4m/s/s and the coasting deceleration of ~0.5m/s/s. */
    val braking: num.Real = -1.0
    /** Turn light on when we are "braking" for 100ms or more. */
    val on    = Sample.Ticks(100.millis)
    /** Turn light off when we are not braking for 400ms.
     * The higher delay here is to limit oscillation to at most 2Hz, which gives
     * a continuous operating life of 14 hours assuming the relay is good for
     * at least 1e5 operations.
     */
    val off   = Sample.Ticks(400.millis)

  /** Main state machine */
  case class Brakes(imu: AccelGyro)(invocation: Node.Invocation) extends Automaton(invocation):
    val light     = output[Bool]
    val ok        = output[Bool]
    val nok_stuck = output[Bool]

    val filter        = subnode(RemoveGravity(imu))

    initial(AWAIT)
    object AWAIT extends State:
      unless {
        restart(filter.valid, OK)
      }
      light     := False
      ok        := Sample.toggle(Sample.Ticks(25))
      nok_stuck := !ok
    object OK extends State:
      unless {
        restart(!filter.valid, AWAIT)

        // BADSOURCE: This should be an "until" transition as it depends on the value of light.
        // For now, delayed by replacing `light` with `fby(False, light)`
        val stuck = Sample.lastN(Brakes.stuck, fby(False, light))
        restart(stuck, STUCK)
      }
      light     := subnode(Lights(filter.accel)).light
      ok        := True
      nok_stuck := False
    object STUCK extends State:
      light     := False
      ok        := False
      nok_stuck := True

    check("not braking, no light") {
      Sample.lastN(Lights.off, filter.accel.y > real(Lights.braking)) ==> !light
    }
    check("invariant") {
      val lights   = Sneaky(OK.builder).subnode("Lights")
      val subcount = lights.subnodes("LastN").last.variable[UInt16]("count") + 0
      val count    = Sneaky(this.builder).subnode("LastN").variable[UInt16]("count") + 0
      OK.active ==>
        ifthenelse(
          light,
          subcount == count,
          subcount <= count
        )
    }


  object Brakes:
    /** Consider the system to be "stuck" if the brake lights are on for more
     * than two minutes. Braking at 1m/s/s from maximum speed of 50m/s should
     * take a bit under a minute, so if we've been braking at >=1m/s/s for two
     * minutes something is wrong. Disengage to avoid spamming the brake lights
     * and desensitising following drivers.
     */
    val stuck = Sample.Ticks(2.minute)

  case class Top(invocation: Node.Invocation) extends Node(invocation):
    val accel = V3(forall[Real], forall[Real], forall[Real])
    val gyro  = V4(forall[Real], forall[Real], forall[Real], forall[Real])
    val imu   = AccelGyro(forall[Bool], accel, gyro)

    subnode(Brakes(imu))
