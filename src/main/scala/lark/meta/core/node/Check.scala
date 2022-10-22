package lark.meta.core.node

import lark.meta.macros.Location
import lark.meta.base.{names, pretty}
import lark.meta.base.names.given
import lark.meta.base.collection.MultiMap
import lark.meta.core.term
import lark.meta.core.term.{Exp, Flow}
import lark.meta.core.Prop.{Form, Judgment}
import lark.meta.core.Sort

import scala.collection.immutable.{SortedMap, SortedSet}

/** Checking and analysis of nodes.
 *
 * Simple typechecking of nodes as well as a guarded analysis.
 * The guardedness analysis is used in Grind.eval to decide which variables
 * should be treated as inputs and which should be checked against the spec.
 *
 * TODO: add better error messages. We can sometimes get away with bad messages
 * because the source typechecker should pick them up first, but it won't catch
 * everything.
 */
object Check:

  /** Options for typechecking programs.
   *
   * @param exp
   *  Term typechecking options including whether to perform integer bounds
   *  checks on literal integers (exp.checkRefinement).
   */
  case class Options(
    exp: term.Check.Options = term.Check.Options(),
  )

  def program(nodes: Iterable[Node], options: Options): names.immutable.RefMap[Info] =
    SortedMap.from(
      nodes.map { n =>
        n.klass -> node(n, options)
      })

  def node(n: Node, options: Options): Info =
    val env  = envOfNode(names.Prefix(List()), n)
    val top  = n.vars.filter { case (c,v) => v.isInput }.keySet
    val visible =
      n.nested.children.map(visibleOfBinding(_))
      .fold(top)(_ ++ _)
    val bind = nested(n, n.nested, top, env, options)
    val vars = takeVariables(bind)
    Info(bind, vars, visible)

  /** Get environment of node */
  def envOfNode(prefix: names.Prefix, node: Node): term.Check.Env =
    // TODO: include internal state in nested contexts for sneaky mode

    val scalars = node.vars.map { case (c,v) =>
      prefix(c) -> v.sort
    }
    val subnodes = node.subnodes.map { case (c,n) =>
      envOfNode(prefix ++ names.Ref.fromComponent(c), n)
    }
    subnodes.fold(SortedMap.from(scalars))(_ ++ _)

  def nested(node: Node, n: Node.Nested, visible: SortedSet[names.Component], env: term.Check.Env, options: Options): Bindings =
    // PERF: this has the wrong complexity - visibleOfBinding should be cached
    // for each level of nesting.
    val visibleX =
      n.children.map(visibleOfBinding(_))
      .fold(visible)(_ ++ _)
    val binds = n.children
      .map(binding(node, _, visibleX, env, options))

    binds.fold(MultiMap.empty[names.Component, Node.Binding.Simple])(_ <> _)


  def binding(n: Node, b: Node.Binding, visible: SortedSet[names.Component], env: term.Check.Env, options: Options): Bindings =
    val envX = env.filter { case (v,s) =>
        visible.contains(v.fullyQualifiedPath.head)
    }
    try
      b match
        case b@ Node.Binding.Equation(lhs, rhs) =>
          term.Check.flow(envX, rhs, options.exp)
          MultiMap.just(lhs, b)
        case b@ Node.Binding.Subnode(sn, args) =>
          val subnode = n.subnodes(sn)
          assert(subnode.params.length == args.length,
            s"Wrong number of args for subnode ${sn.pprString}: got ${pretty.layout(pretty.tupleP(args))}, want ${pretty.layout(pretty.tupleP(subnode.params))}")
          subnode.params.zip(args).foreach { case (param, arg) =>
            term.Check.exp(envX, arg, options.exp)
            val paramS = subnode.vars(param).sort
            assert(arg.sort == paramS,
              s"Wrong argument type for parameter ${param.pprString} of subnode ${sn.pprString}: got ${arg.pprString}, want ${paramS.pprString}")
          }
          MultiMap.just(sn, b)
        case Node.Binding.Reset(k, nest) =>
          term.Check.exp(envX, k, options.exp)
          assert(k.sort == Sort.Bool,
            s"Reset clock should be a bool, got ${k.sort.pprString} for clock ${k.pprString}")
          nested(n, nest, visible, env, options)
        case Node.Binding.Merge(cases) =>
          val binds = cases.map { case (k,nest) =>
            term.Check.exp(envX, k, options.exp)
            assert(k.sort == Sort.Bool,
              s"Merge clock should be a bool, got ${k.sort.pprString} for clock ${k.pprString}")
            nested(n, nest, visible, env, options)
          }
          binds.fold(MultiMap.empty[names.Component, Node.Binding.Simple])(_ <> _)
    catch
      case e: term.Check.except.NoSuchVariableException =>
        if env.contains(e.e.v)
        then
          val c = e.e.v.fullyQualifiedPath.head
          val anyBinding = n.allSubnesteds.exists { case (n,p) => n.bindings.contains(c) }
          val v = pretty.squote <> e.e.ppr <> pretty.squote <> n.vars.get(c).fold(pretty.emptyDoc)(v => v.location.ppr(" "))
          if anyBinding
          then
            throw new Exception(
              s"""Variable ${pretty.layout(v)} used outside its scope.
                 |This variable is defined within a merge context, but as it is not defined
                 |in all cases of the merge, it is not available outside the merge.
                                                                |It may be missing definitions in some cases.""".stripMargin,
              e)
          else
            throw new Exception(
              s"""Variable ${pretty.layout(v)} missing definition.
                 |The variable is declared but has no definition.
                 |If it really doesn't need a definition, then try declaring it with forall.""".stripMargin,
              e)
        else throw e
      case e: Exception =>
        // TODO need better source locations
        val where =
          b match
            case b@ Node.Binding.Equation(lhs, _) =>
              pretty.text("in definition at ") <> n.vars(lhs).location.ppr
            case b@ Node.Binding.Subnode(sn, _) =>
              val nn = n.subnodes(sn)
              pretty.text("in invocation of subnode") <+> sn.ppr <+> pretty.parens(nn.klass.ppr)
            case b@ Node.Binding.Merge(_) =>
              pretty.text("in merge")
            case b@ Node.Binding.Reset(k, _) =>
              pretty.text("in reset with clock") <+> k.ppr
        throw new Exception(pretty.layout(where), e)

  def visibleOfBinding(binding: Node.Binding): SortedSet[names.Component] = binding match
    case Node.Binding.Equation(lhs, _) => SortedSet(lhs)
    case Node.Binding.Subnode(lhs, _) => SortedSet(lhs)
    case Node.Binding.Reset(_, nested) => visibleOfNested(nested)
    case Node.Binding.Merge(cases) =>
      val vis = cases.map { case (k,n) =>
        visibleOfNested(n)
      }
      vis match
        case Nil => SortedSet.empty
        case _ => vis.reduce { (a,b) => a.intersect(b) }

  def visibleOfNested(n: Node.Nested): SortedSet[names.Component] =
    n.children.map(visibleOfBinding(_)).fold(SortedSet.empty[names.Component])(_ ++ _)


  case class Info(
    bindings: Bindings,
    variables: Variables,
    toplevel: names.immutable.ComponentSet
  ):
    /** Check if a variable has no definition and so should be treated like
     * an input for evaluation */
    def isUnconstrained(name: names.Component): Boolean =
      !bindings.entries.contains(name) && toplevel(name)

    /** Check if a variable is well-defined, which means that it is guarded
     * and has a definition. */
    def isWellDefined(name: names.Component): Boolean =
      variables.contains(name) && !variables(name).unguarded && toplevel(name)


  /** Information about a local variable.
   *
   * @param unguarded
   *  true if this variable mentions an unguarded pre variable that could have
   *  an undefined value
   */
  case class Var(
    unguarded: Boolean,
  )

  type Bindings = MultiMap[names.Component, Node.Binding.Simple]
  type Variables = names.immutable.ComponentMap[Var]

  def takeVariable(binds: Bindings, vars: Variables, name: names.Component, bs: List[Node.Binding]): Variables =
    if vars.contains(name)
    then vars
    else
      val any_pre = bs.exists { b => b match
        case Node.Binding.Equation(_, Flow.Pre(_)) => true
        case _ => false
      }
      val all_deps =
        bs.flatMap(freeB(_))

      val vars0 = vars + (name -> Var(unguarded = any_pre))

      val varsX = all_deps.foldLeft(vars0) { (varsX, c) =>
        takeVariable(binds, varsX, c, binds(c))
      }

      val any_unguarded = all_deps.exists(c => varsX(c).unguarded)

      varsX + (name -> Var(unguarded = any_pre || any_unguarded))

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
    case v: (Node.Binding.Merge | Node.Binding.Reset) =>
      lark.meta.base.assertions.impossible("freeB should not be called with contexts", "binding" -> b)

  def freeE(e: Exp): Seq[names.Component] = for
    v <- term.Compound.take.vars(e)
    Exp.Var(_, names.Ref(prefix, c)) = v
    if prefix.isEmpty
  yield c
