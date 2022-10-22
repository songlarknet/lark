package lark.meta.source.node

import lark.meta.source.Stream

import java.lang.reflect.Field
import scala.reflect.ClassTag

/** Optional reflective magic for invoking subnodes with "fresh" arguments.
 *
 * For separate compilation and modular proofs, we need to enforce the
 * distinction between a node's parameters at the definition, and the actual
 * arguments at the call-site. This distinction gets a bit blurry when we're
 * passing simple values to nodes, such as
 *
 * > class N(reset: Stream[Bool], trigger: Stream[Bool]) extends Node
 *
 * When we call this with N(False, True), we need some way to associate...
 */
object Magic:
  def freshen[T <: Base : ClassTag](target: Base, invocation: Invocation)(using location: lark.meta.macros.Location): T =
    val klass  = target.getClass()
    def err(str: String) =
      s"""Magic.freshen: cannot invoke node ${klass.getSimpleName()}:
         |  $str
         |Invocation ${location.pprString}""".stripMargin

    // assert (!target.isInstanceOf[Product],
    //   err("Nodes should be case classes."))

    val ctors  = klass.getConstructors()
    assert(ctors.length == 1,
      s"Nodes should only have one constructor.")

    val ctor   = ctors(0)
    val args = ctor.getParameters().map { p =>
      if p.getType() == summon[ClassTag[Invocation]].runtimeClass
      then invocation
      else
        val name  = p.getName()
        val field = klass.getDeclaredField(name)
        field.setAccessible(true)
        field.get(target) match
          case s: Stream[_] =>
            invocation.stream(name, s.asInstanceOf[Stream[Any]])
          case f: Invocation.Freshen =>
            f.freshen(name, invocation)
          case o: Object =>
            invocation.meta(name, o)
    }
    ctor.newInstance(args : _*).asInstanceOf[T]

  /** Check if a node has arguments. If not, it's OK to have no arguments in the invocation. */
  def nodeHasArguments(target: Base): Boolean =
    val klass  = target.getClass()
    val ctors  = klass.getConstructors()
    ctors.exists { c =>
      c.getParameters().exists { p =>
        p.getType() != summon[ClassTag[Invocation]].runtimeClass
      }
    }


  def forceObjects[T <: Product](node_ : T): Unit =
    // TODO Instantiate all objects
    val klass = node_.getClass()
    klass.getDeclaredMethods().foreach { f =>
      println(s"Declared methods: $f, ${f.getName()}, ${f.isAccessible()}, ${f.getParameterCount()}")
      if f.getParameterCount() == 0 then
        println("Calling")
        f.invoke(this)
    }