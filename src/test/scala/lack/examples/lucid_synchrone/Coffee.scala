package lack.examples.lucid_synchrone

import lack.meta.base.num.Integer

import lack.meta.source.Compound.{given, _}
import lack.meta.source.Compound.implicits._
import lack.meta.source.Automaton
import lack.meta.source.Node
import lack.meta.source.Stream
import lack.meta.source.Stream.{SortRepr, Bool, UInt8, UInt16, Int32}
import lack.meta.driver.{Check, Compile, Grind}

/** Fast tests */
class Coffee_Check extends munit.FunSuite:
  test("Check") {
    Check.success() { Coffee.Top(_) }
  }

  test("Compile") {
    Compile.compile(
      basename = "coffee",
      output = Some(java.nio.file.Paths.get("scratch/c/")))
      { Coffee.Top(_) }
  }

/** Slow tests */
class Coffee_Grind extends munit.FunSuite:
  test("Grind") {
    Grind.grind(Grind.Options(count = 10)) { Coffee.Top(_) }
  }

/** Coffee machine loosely translated from Lucid-Synchrone manual:
 * https://www.di.ens.fr/~pouzet/lucid-synchrone/manual_html/manual020.html
 */
object Coffee:

  /** The opaque datatypes are defined in a local context.
   * The implementations of these types are only visible inside the context.
   * There's a lot of boilerplate here but it should be easy to generate.
   */
  object Types:
    // I've translated the types as optional types by adding a "None" value.
    opaque type Coin = Stream.UInt8
    object Coin:
      val None:   Stream[Coin] = u8(0)
      val Dime:   Stream[Coin] = u8(1)
      val Nickel: Stream[Coin] = u8(2)
      def valid(i: Stream[Coin])(using builder: Node.Builder, location: lack.meta.macros.Location): Stream[Bool] =
        i == None || i == Dime || i == Nickel

    given SortRepr[Coin] = Stream.SortRepr_UInt8

    opaque type Drink = Stream.UInt8
    object Drink:
      val None:   Stream[Drink] = u8(0)
      val Coffee: Stream[Drink] = u8(1)
      val Tea:    Stream[Drink] = u8(2)
      def valid(i: Stream[Drink])(using builder: Node.Builder, location: lack.meta.macros.Location): Stream[Bool] =
        i == None || i == Coffee || i == Tea

    given SortRepr[Drink] = Stream.SortRepr_UInt8

    opaque type Button = Stream.UInt8
    object Button:
      val None:   Stream[Button] = u8(0)
      val Coffee: Stream[Button] = u8(1)
      val Tea:    Stream[Button] = u8(2)
      val Cancel: Stream[Button] = u8(3)
      def valid(i: Stream[Button])(using builder: Node.Builder, location: lack.meta.macros.Location): Stream[Bool] =
        i == None || i == Coffee || i == Tea || i == Cancel

    given SortRepr[Button] = Stream.SortRepr_UInt8

    opaque type Currency = Stream.UInt32
    object Currency:
      def apply(i: Integer): Stream[Currency] = u32(i)
      def MAX = Currency(1000)
    given SortRepr[Currency] = Stream.SortRepr_UInt32
    given Num[Currency] = Num_UInt32

  /** Import the interface of the declared datatypes (without the implementation details) */
  import Types._


  case class Vend(drink: Stream[Drink], cost: Stream[Currency], v: Stream[Currency])(invocation: Node.Invocation) extends Node(invocation):
    requires("Valid drink") { drink != Drink.None }

    val emit      = output[Drink]
    val spent     = output[Currency]
    val remaining = output[Currency]

    remaining := v - spent

    new Merge(v >= cost):
      new When(True):
        emit  := drink
        spent := cost
      new When(False):
        emit  := Drink.None
        spent := 0

  case class Coffee(coin: Stream[Coin], button: Stream[Button])(invocation: Node.Invocation) extends Node(invocation):
    val currency     = output[Currency]

    val income       = output[Currency]
    val spent        = output[Currency]
    val refund       = output[Currency]

    val emit         = output[Drink]

    income := select(
      when(coin == Coin.Dime)   { Currency(5) },
      when(coin == Coin.Nickel) { Currency(10) },
      otherwise                 { Currency(0) }
    )

    val pre_currency = fby(Currency(0), currency)
    currency := pre_currency + income - refund - spent

    new Merge(pre_currency + income > Currency.MAX):
      // The original has a (very unlikely) integer overflow - you can keep
      // inserting coins until the amount overflows. Here, if the amount would
      // go over $10.00 then we refund everything.
      new When(True):
        emit     := Drink.None
        refund   := pre_currency + income
        spent    := 0
      new When(False):
        new Merge(button):
          new When(Button.None):
            refund   := 0
            spent    := 0
            emit     := Drink.None
          new When(Button.Coffee):
            val vend  = subnode(Vend(Drink.Coffee, Currency(10), pre_currency))
            spent    := vend.spent
            emit     := vend.emit
            refund   := 0
          new When(Button.Tea):
            val vend  = subnode(Vend(Drink.Tea, Currency(5), pre_currency))
            spent    := vend.spent
            emit     := vend.emit
            refund   := 0
          new When(Button.Cancel):
            spent    := 0
            emit     := Drink.None
            refund   := pre_currency + income

    requires("Valid coin")   { Coin.valid(coin) }
    requires("Valid button") { Button.valid(button) }
    check("Refund: all or nothing") {
        refund == pre_currency + income || refund == 0
    }
    check("Spending iff emitting") {
        (spent > 0) == (emit != Drink.None)
    }
    check("No spontaneous emitting") {
        (emit != Drink.None) ==> (button != Button.None)
    }

  case class Top(invocation: Node.Invocation) extends Node(invocation):
    val coin   = forall[Coin]
    val button = forall[Button]

    requires("Valid coin")   { Coin.valid(coin) }
    requires("Valid button") { Button.valid(button) }

    subnode(Coffee(coin, button))
