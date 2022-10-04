package lack.meta.core.node

import lack.meta.macros.Location
import lack.meta.base.{names, pretty}
import lack.meta.base.names.given
import lack.meta.base.collection.MultiMap
import lack.meta.core.term
import lack.meta.core.term.{Exp, Flow}
import lack.meta.core.Prop.{Form, Judgment}

import scala.collection.immutable.SortedMap

/** Checking and analysis of nodes.
 *
 * Right now this is just a small analysis to determine which variables have
 * no definition, and which variables are well-defined with no unguarded
 * pres. It's used in Grind.eval to decide which variables should be treated
 * as inputs and which should be checked against the spec.
 * TODO: implement type-checker
 */
object Check:

  case class Info(
    bindings: Bindings,
    variables: Variables
  ):
    /** Check if a variable has no definition and so should be treated like
     * an input for evaluation */
    def isUnconstrained(name: names.Component): Boolean =
      variables(name).paths.isEmpty

    /** Check if a variable is well-defined, which means that it is guarded
     * and has a definition.
     * TODO: this should treat variables defined in all arms of a many-armed
     * merge as well-defined. */
    def isWellDefined(name: names.Component): Boolean =
      val v = variables(name)
      !v.unguarded && v.paths == List(List())


  def info(node: Node): Info =
    val b = takeBindings(node)
    val v = takeVariables(b)
    Info(b, v)


  /** Information about a local variable.
   *
   * @param unguarded
   *  true if this variable mentions an unguarded pre variable that could have
   *  an undefined value
   * @param paths
   *  list of paths where this variable has a definition
   */
  case class Var(
    unguarded: Boolean,
    paths: List[Node.Path],
  )

  type Bindings = MultiMap[names.Component, (Node.Path, Node.Binding)]
  type Variables = names.immutable.ComponentMap[Var]

  def takeBindings(node: Node): Bindings =
    val binds =
      for
        (nest,path) <- node.allSubnesteds
        c <- nest.bindings
      yield
        MultiMap.just(c._1, (path, c._2))
    MultiMap.concat(binds)

  def takeVariable(binds: Bindings, vars: Variables, name: names.Component, pbs: List[(Node.Path, Node.Binding)]): Variables =
    if vars.contains(name)
    then vars
    else
      val any_pre = pbs.exists { case (_,b) => b match
        case Node.Binding.Equation(_, Flow.Pre(_)) => true
        case _ => false
      }
      val paths = pbs.map(_._1)
      val all_deps =
        for
          (p, b) <- pbs
          c <- freeB(b)
        yield
          c

      val vars0 = vars + (name -> Var(unguarded = any_pre, paths = paths))

      val varsX = all_deps.foldLeft(vars0) { (varsX, c) =>
        takeVariable(binds, varsX, c, binds(c))
      }

      val any_unguarded = all_deps.exists(c => varsX(c).unguarded)

      varsX + (name -> Var(unguarded = any_pre || any_unguarded, paths = paths))

  def takeVariables(binds: Bindings): Variables =
    binds.entries.foldLeft(SortedMap.empty[names.Component, Var]) { (acc, b) =>
      takeVariable(binds, acc, b._1, b._2)
    }


  def freeB(b: Node.Binding): Seq[names.Component] = b match
    case Node.Binding.Equation(lhs, rhs) => rhs match
      case Flow.Pure(e) => freeE(e)
      case Flow.Arrow(first, _) => freeE(first)
      case Flow.Pre(e) => Nil
      case Flow.Fby(_, _) => Nil
    case Node.Binding.Subnode(n, args) =>
      for
        a <- args
        c <- freeE(a)
      yield c

  def freeE(e: Exp): Seq[names.Component] = for
    v <- term.Compound.take.vars(e)
    Exp.Var(_, names.Ref(prefix, c)) = v
    if prefix.isEmpty
  yield c
