package lark.meta.core.node.analysis

import lark.meta.base.{pretty, names, debug}
import lark.meta.base.names.given
import lark.meta.base.collection.MultiMap
import lark.meta.base.collection.mutable.EGraph
import lark.meta.base.collection.mutable.EGraph.Tree

import lark.meta.core
import lark.meta.core.Sort
import lark.meta.core.term
import lark.meta.core.term.{Exp, Flow, Compound, Val}
import lark.meta.core.node
import lark.meta.core.node.Node

import scala.collection.immutable
import scala.collection.mutable

object Equivalence:
  /** The equivalence graphs are composed of nodes where each node has an
   * operator (Op) applied to a possibly empty list of arguments. Each argument
   * refers to an equivalence class.
   * To translate streaming programs into this form, we represent variables
   * and values as their own operators with no arguments.
   * Primitive applications such as `x + y` become `map(+)(x, y)` to emphasise
   * that the primitive represents an element-wise application on two input
   * streams.
   * Flow expressions become `pre(x)` or `arrow(x, y)`.
   * We represent recursion in the core program as a µ binding form with
   * de Bruijn indices, so that the recursive binding
   * > count = (0 -> pre count) + input
   * becomes
   * > count = µ. (0 -> pre µ0) + input
   *
   * The nameless de Bruijn representation ensures that alpha-equivalent
   * recursive bindings look the same.
   */
  sealed trait Op extends pretty.Pretty:
    def isLeaf: Boolean
  object Op:
    /** Variable occurrence. Argument list should be empty. */
    case class Var(v: names.Ref) extends Op:
      def ppr = v.ppr
      def isLeaf = true

    /** Value. Argument list should be empty. */
    case class Val(v: term.Val) extends Op:
      def ppr = v.ppr
      def isLeaf = true

    /** Primitive application. */
    case class Prim(prim: term.Prim) extends Op:
      def ppr = prim.ppr
      def isLeaf = false

    /** Streaming `pre` */
    case object Pre extends Op:
      def ppr = pretty.text("pre")
      def isLeaf = false

    /** Streaming arrow `x -> y` */
    case object Arrow extends Op:
      def ppr = pretty.text("arrow")
      def isLeaf = false

    /** Recursive binding */
    case object MuBinder extends Op:
      def ppr = pretty.text("µ.")
      def isLeaf = false

    /** Reference to recursive binder.
     * The level is the de Bruijn index, specifying how many other µ-binders
     * occur between this reference and the binder.
     * For many recursive binders there's only one binder, so:
     * > sum = (0 -> pre sum) + e
     * becomes
     * > sum = µ. (0 -> pre µ0) + e
     *
     * Mutually recursive bindings can be more interesting:
     * > rec0 = rec1 + (0 -> pre rec0)
     * > rec1 = pre rec0 + (0 -> pre rec1)
     * should become:
     * > rec0 = µ. (µ. pre µ1 + (0 -> pre µ0)) + (0 -> pre µ0)
     * > rec1 = µ. pre (µ. µ1 + (0 -> pre µ0)) + (0 -> pre µ0)
     */
    case class MuVar(level: Int) extends Op:
      def ppr = pretty.text("µ") <> pretty.value(level)
      def isLeaf = true


  /** A "layer" is a set of equations that all operate on the same clock. The
   * equations include those from inside subnodes.
   *
   * @param equations
   *  a set of bindings that all have the same clock
   * @param boring
   *  an egraph constructed from the bindings, but with no interesting
   *  rewrites applied to it
   * @param interesting
   *  an egraph with interesting rewrites applied
   */
  class Layer(
    val inits: mutable.ArrayBuffer[names.Ref] = mutable.ArrayBuffer[names.Ref](),
    val equations: names.mutable.RefMap[Flow] = mutable.SortedMap[names.Ref, Flow](),
    val boring: EGraph[Op] = EGraph[Op](),
    val interesting: EGraph[Op] = EGraph[Op](),
  ) extends pretty.Pretty:
    def ppr =
      val equationsP = equations.map { (r,f) =>
        r.ppr <+> pretty.text("=") <+> f.ppr
      }
      val invariantsP = invariants.map { inv =>
        pretty.braces(pretty.space <> pretty.ssep(inv.map(_.ppr), pretty.comma <> pretty.space) <> pretty.space)
      }
      pretty.vsep(Seq(
        pretty.text("Init flags:"),
        pretty.indent(pretty.hsep(inits.map(_.ppr).toSeq)),
        pretty.text("Equations:"),
        pretty.indent(pretty.vsep(equationsP.toSeq)),
        pretty.text("Boring e-graph:"),
        pretty.indent(boring.ppr),
        pretty.text("Interesting e-graph:"),
        pretty.indent(interesting.ppr),
        pretty.text("Invariants:"),
        pretty.indent(pretty.vsep(invariantsP)),
      ))

    /** Convert named recursion to µ-bindings */
    def normalise(): Unit =
      // Transitive and direct dependencies for each binding
      val mpDeps  = mutable.SortedMap[names.Ref, names.immutable.RefSet]()
      val graph   = this.interesting

      val empty = immutable.SortedSet[names.Ref]()

      // LODO: this is a bit shaky for mutual recursion; see TestMutualRecursion.scala:rec0-rec1
      /** Unfold a reference */
      def unfoldR(ref: names.Ref, stop: names.Ref, deps: names.immutable.RefSet): (EGraph.Id, names.immutable.RefSet) =
        val depsX = deps + ref
        if deps.contains(ref)
        then (graph.add(Op.Var(ref)), deps)
        else if ref == stop
        then
          mpDeps += ref -> deps
          (graph.add(Op.MuVar(0)), depsX)
        else
          mpDeps.get(ref) match
            case Some(refDeps) =>
              if refDeps.contains(stop)
              then unfoldF(this.equations(ref), stop, depsX)
              else (graph.add(Op.Var(ref)) , refDeps)
            case None =>
              this.equations.get(ref) match
                case Some(flow) =>
                  val (id, depsXX) = unfoldF(flow, stop, depsX)
                  mpDeps += ref -> depsXX
                  (id, depsXX)
                case None =>
                  mpDeps += ref -> empty
                  (graph.add(Op.Var(ref)), empty)

      def unfoldE(exp: Exp, stop: names.Ref, deps: names.immutable.RefSet): (EGraph.Id, names.immutable.RefSet) = exp match
        case Exp.App(_, prim, args*) =>
          val (argsX, depssX) = args.map(unfoldE(_, stop, deps)).unzip
          val depsX = depssX.fold(empty)(_ ++ _)
          val op = Op.Prim(prim)
          val id = graph.add(op, argsX*)
          (id, depsX)
        case v: Exp.Var =>
          unfoldR(v.v, stop, deps)
        case Exp.Val(v) =>
          (insertTerm(graph, v), empty)
        case Exp.Cast(_, e) =>
          unfoldE(e, stop, deps)

      def unfoldF(flow: Flow, stop: names.Ref, deps: names.immutable.RefSet): (EGraph.Id, names.immutable.RefSet) = flow match
        case Flow.Pure(e) =>
          unfoldE(e, stop, deps)
        case Flow.Fby(v, e) =>
          val (id1, depsX1) = unfoldE(Exp.Val(v), stop, deps)
          val (id2, depsX2) = unfoldE(e, stop, deps)
          (graph.add(Op.Arrow, id1, graph.add(Op.Pre, id2)), depsX1 ++ depsX2)
        case Flow.Pre(e) =>
          val (id, depsX) = unfoldE(e, stop, deps)
          (graph.add(Op.Pre, id), depsX)
        case Flow.Arrow(e1, e2) =>
          val (id1, depsX1) = unfoldE(e1, stop, deps)
          val (id2, depsX2) = unfoldE(e2, stop, deps)
          (graph.add(Op.Arrow, id1, id2), depsX1 ++ depsX2)

      this.equations.foreach { (ref,flow) =>
        val (id, deps) = unfoldF(flow, ref, empty)
        if deps.contains(ref) then
          val mubind = graph.add(Op.MuBinder, id)
          val refC = graph.add(Op.Var(ref))
          graph.merge(refC, mubind)
      }

      graph.rebuild()

    /** Get the "interesting" invariants */
    def invariants: List[List[Tree[Op]]] =
      // Clone the boring graph. We use it to decide which invariants are
      // novel. We update it when adding new invariants to avoid having too
      // many duplicates of the same fact
      val g0   = boring.clone()
      val invs = mutable.ArrayBuffer[List[Tree[Op]]]()
      // TODO: invariants should only refer to state variables and values
      // because they retain their value even when the clock is off
      val classes = interesting.classes
      // Try to add invariants for small terms before looking at larger ones
      Seq(0, 1, 2, Int.MaxValue).foreach { maxDepth =>
        classes.foreach { (klass, nodes) =>
          val ns = takeSimpleTrees(g0, classes, klass, maxDepth)
          if ns.length > 1
          then
            // Record invariant and merge them so we don't record it again
            invs += ns
            ns.map(g0.add(_)).reduce(g0.merge(_, _))
            g0.rebuild()
        }
      }
      invs.toList

    def takeSimpleTrees(g0: EGraph[Op], classes: mutable.SortedMap[EGraph.Id, mutable.HashSet[EGraph.Node[Op]]], klass: EGraph.Id, maxDepth: Int): List[Tree[Op]] =
      val trees = classes.getOrElse(klass, mutable.HashSet()).flatMap { n =>
        n.op match
          case Op.Val(_) => List(Tree(n.op))
          case Op.Var(_) => List(Tree(n.op))
          case Op.Prim(p)
           if maxDepth > 0 =>
            val childrenX = n.children.map(takeSimpleTrees(g0, classes, _, maxDepth - 1))
            listCombine(childrenX).map { c => Tree(n.op, c) }
          // Ignore flow expressions arrow and pre - prefer the named reference.
          case _ => List()
      }
      // Remove duplicates that are already known to be equal by the e-graph
      trees.toList.distinctBy(g0.add(_))

    /** Possible combinations of sublists:
     * > List(List(1, 2), List(3, 4)) = List(List(1, 3), List(1, 4), List(2, 3), List(2, 4))
     * This grows very quickly, but in practice it's only used with ls.length <= 3.
     */
    def listCombine[T](ls: List[List[T]]): List[List[T]] = ls match
      case Nil => List(List())
      case xs :: xss =>
        val xssX = listCombine(xss)
        xs.flatMap { x =>
          xssX.map { xs =>
            x :: xs
          }
        }

  class Layers(
    val node: Node,
    val layers: mutable.HashMap[Node.Path, Layer] = mutable.HashMap[Node.Path, Layer]()
  ) extends pretty.Pretty:

    def ppr =
      val layersP = layers.map { (p,l) =>
        val pathP = pretty.ssep(p.map(_.ppr), pretty.space <> pretty.forwslash <> pretty.space)
        pretty.text("Layer") <+> pathP <> pretty.colon <@> pretty.indent(l.ppr)
      }
      val invariantsP = invariants.map(_.ppr)
      node.klass.ppr <> pretty.colon <@>
      pretty.indent(pretty.vsep(layersP.toSeq)) <@>
      pretty.indent(pretty.text("Invariant terms:") <@>
        pretty.indent(pretty.vsep(invariantsP)))

    def layer(p: Node.Path): Layer =
      layers.getOrElseUpdate(p, Layer())

    /** Assemble the layers from subnodes' layers as well as the current
     * node's bindings. */
    def assemble(mpNodeLayers: names.mutable.RefMap[Layers]): Unit =
      val (equations, subnodes) = bindingsOfNode(node)

      // Include layers from all of the subnodes
      subnodes.foreach { (path, subnodesX) =>
        subnodesX.foreach { (c,b) =>
          val prefix = names.Prefix(List(c))
          val sn = node.subnodes(c)
          val snLayers = mpNodeLayers(sn.klass)
          sn.params.zip(b.args).foreach { (param, arg) =>
            val layerX = layer(path)
            val ref = prefix(param)
            layerX.equations += (ref -> Flow.Pure(arg))
            val i = insertTerm(layerX.boring, arg)
            layerX.boring.merge(layerX.boring.add(Op.Var(ref)), i)
            val s = insertTerm(layerX.interesting, arg)
            layerX.interesting.merge(layerX.interesting.add(Op.Var(ref)), s)
          }
          snLayers.layers.foreach { (snPath, snLayer) =>
            val pathX = path ++ snPath.map(pe => pe.mapX(e => Compound.substVV(prefix(_), e)))
            val layerX = layer(pathX)

            layerX.inits ++= snLayer.inits.map(prefix(_))

            snLayer.equations.foreach { (ref, eqn) =>
              layerX.equations += prefix(ref) -> Compound.substVV(prefix(_), eqn)
            }
            appendEGraph(prefix, snLayer.boring, layerX.boring)
            appendEGraph(prefix, snLayer.interesting, layerX.interesting)
          }
        }
      }

      // Add a constraint for each equation
      equations.foreach { (path, equationsX) =>
        val layerX = layer(path)
        equationsX.foreach { (c, flow) =>
          val ref = names.Ref.fromComponent(c)
          layerX.equations += ref -> flow
          for (g <- Seq(layerX.boring, layerX.interesting)) {
            val id = insertTerm(g, flow)
            g.merge(g.add(Op.Var(ref)), id)
          }
        }
      }

      // Add INIT flags for each nested context
      node.allSubnesteds.foreach { (nested, path) =>
        nested.INIT.foreach { init =>
          val layerX = layer(path)
          layerX.inits += init
          // Add a binding `init = true -> false`, but only add it to the
          // interesting graph because it's not clear from the transition
          // system alone.
          val g = layerX.interesting
          // TODO: add init when typechecking environment includes init flags
          // val i = g.add(Op.Arrow, g.add(Op.Val(Val.Bool(true))), g.add(Op.Val(Val.Bool(false))))
          // g.merge(i, g.add(Op.Var(init)))
        }
      }

      layers.foreach { (path, layer) =>
        layer.boring.rebuild()
        layer.interesting.rebuild()
      }

    /** Normalise expressions, converting named recursion to locally-nameless
     * µ-bindings.
     *
     * To extract all of the recursive bindings we need to look through all
     * of the bindings, including the subnodes' bindings, because we could
     * have some recursion that goes through multiple nodes.
     */
    def normalise(): Unit =
      layers.foreach { (p,l) =>
        l.normalise()
      }


    /** Turn the crank until we have saturated */
    def crank(): Unit =
      // TODO: do interesting work
      ()

    /** Get invariants of all layers as pure expressions */
    def invariants: List[Exp] =
      val env = core.node.Check.envOfNode(names.Prefix(), this.node)
      val invs = layers.values.flatMap { l =>
        l.invariants
      }.toList
      invs.map { trees =>
        val exps = trees.map(expOfTree(env, _))
        exps.zip(exps.drop(1)).map { (l,r) =>
          Compound.app(term.prim.Table.Eq, l, r)
        }.reduce { (l,r) =>
          Compound.app(term.prim.Table.And, l, r)
        }
      }

    def expOfTree(env: term.Check.Env, tree: Tree[Op]): Exp = tree.op match
      case Op.Val(v) => Exp.Val(Val.unwrap(v))
      case Op.Var(v) =>
        val t = env(v)
        val e = Compound.var_(t, v)
        t match
          case _ : Sort.Refinement =>
            Compound.unbox(e)
          case _ =>
            e
      case Op.Prim(p) =>
        Compound.app(p, tree.children.map(expOfTree(env, _))*)
      case _ =>
        lark.meta.base.assertions.impossible(
          "expOfTree: cannot convert operator to pure expression",
          "op"   -> tree.op,
          "tree" -> tree)


  def program(nodes: List[Node], dump: debug.Options, stage: debug.Stage): names.immutable.RefMap[Layers] =
    val mpNodeLayers = mutable.SortedMap[names.Ref, Layers]()
    nodes.foreach { n =>
      val layers = node(n, mpNodeLayers)
      dump.traceP(layers, stage, Some(n.klass.pprString))
      mpNodeLayers += n.klass -> layers
    }
    immutable.SortedMap.from(mpNodeLayers)


  def node(node: Node, mpNodeLayers: names.mutable.RefMap[Layers]): Layers =
    val layers = Layers(node)
    layers.assemble(mpNodeLayers)
    layers.normalise()
    layers.crank()
    layers

  def insertTerm(graph: EGraph[Op], value: Val): graph.Class =
    graph.add(Op.Val(Val.unwrap(value)))

  def insertTerm(graph: EGraph[Op], exp: Exp): graph.Class = exp match
    case Exp.App(_, prim, args*) =>
      val argsX = args.map(insertTerm(graph, _))
      val op = Op.Prim(prim)
      graph.add(op, argsX*)
    case v: Exp.Var =>
      graph.add(Op.Var(v.v))
    case Exp.Val(v) =>
      insertTerm(graph, v)
    case Exp.Cast(_, e) =>
      insertTerm(graph, e)

  def insertTerm(graph: EGraph[Op], flow: Flow): graph.Class = flow match
    case Flow.Pure(e) =>
      insertTerm(graph, e)
    case Flow.Fby(v, e) =>
      val vX  = insertTerm(graph, v)
      val eX  = insertTerm(graph, e)
      val pre = graph.add(Op.Pre, eX)
      val arr = graph.add(Op.Arrow, vX, pre)
      arr
    case Flow.Pre(e) =>
      graph.add(Op.Pre, insertTerm(graph, e))
    case Flow.Arrow(a, b) =>
      graph.add(Op.Arrow, insertTerm(graph, a), insertTerm(graph, b))


  /** Append a subnode graph (source) into the destination graph (dest). Any
   * variable references in the subnode graph are prefixed with the prefix. */
  def appendEGraph(prefix: names.Prefix, source: EGraph[Op], dest: EGraph[Op]): Unit =
    // Mapping from e-classes in the source to e-classes in the destination
    val destClass = mutable.HashMap[source.Class, dest.Class]()
    var v = dest.version - 1
    // Run to a fixpoint until we stop changing the destination.
    while (v != dest.version)
      v = dest.version
      source.classes.foreach { (klass, enodes) =>
        val nodesX = enodes.map { n =>
          try
            // Check if all child classes have been copied. If not, catch
            // exception and skip this one for now.
            val childrenX = n.children.map(destClass(_))
            val opX = n.op match
              case Op.Var(ref) =>
                Op.Var(prefix(ref))
              case op =>
                op

            val put = dest.add(opX, childrenX*)
            destClass.get(klass) match
              case Some(destClassX) =>
                dest.merge(put, destClassX)
                dest.rebuild()
              case None =>
                destClass += (klass -> put)
          catch
            // Skip
            case _: NoSuchElementException =>
        }
      }

  def bindingsOfNode(node: Node): (mutable.HashMap[Node.Path, names.mutable.ComponentMap[Flow]], mutable.HashMap[Node.Path, names.mutable.ComponentMap[Node.Binding.Subnode]]) =
    val equations = mutable.HashMap[Node.Path, names.mutable.ComponentMap[Flow]]()
    val subnodes  = mutable.HashMap[Node.Path, names.mutable.ComponentMap[Node.Binding.Subnode]]()

    node.allSubnesteds.foreach { (n,p) =>
      n.bindings.foreach { (c,b) =>
        b match
          case Node.Binding.Equation(_, flow) =>
            equations.getOrElseUpdate(p, mutable.SortedMap()) += (c -> flow)
          case b: Node.Binding.Subnode =>
            subnodes.getOrElseUpdate(p, mutable.SortedMap()) += (c -> b)
      }
    }
    (equations, subnodes)
