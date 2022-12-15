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

  /** Options for equivalence analysis
   * @param fix
   *  maximum number of iterations to perform rewrites for
   * @param invariantTermMaxHeight
   *  only consider invariants with terms up to this height. Simple invariants
   *  that relate two node applications as being equivalent have height 0, as
   *  the state variables are considered height 0 and the equality operator is
   *  not included in the height of the invariant term.
   *  More interesting invariants need larger heights, for example the
   *  invariant that tells us that
   *  > SoFar(X and Y) = SoFar(X) and SoFar(Y)
   *  would look like this, which requires a height of 1:
   *  > SoFar?0.state = SoFar?1.state and SoFar?2.state
   *
   *  Extracting the invariants involves exploring all possible ways to write
   *  expressions up to a given height, so larger heights can get exponentially
   *  slower. Five seems like a reasonable default so far; set it to zero to
   *  improve extraction speed.
   */
  case class Options(
    fix: EGraph.FixOptions = EGraph.FixOptions(),
    invariantTermMaxHeight: Int = 5
  )

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
   * @param options
   * @param inits
   *  all of the init flags in the nested contexts at this clock layer
   * @param equations
   *  a set of bindings that all have the same clock
   * @param boring
   *  an egraph constructed from the bindings, but with no interesting
   *  rewrites applied to it
   * @param interesting
   *  an egraph with interesting rewrites applied
   */
  class Layer(
    val path: Node.Path,
    val options: Options,
    val inits: mutable.ArrayBuffer[names.Ref] = mutable.ArrayBuffer[names.Ref](),
    val equations: names.mutable.RefMap[Flow] = mutable.SortedMap[names.Ref, Flow](),
    val boring: EGraph[Op] = EGraph[Op](),
    val interesting: EGraph[Op] = EGraph[Op](),
    val invariants: mutable.ArrayBuffer[List[Tree[Op]]] = mutable.ArrayBuffer[List[Tree[Op]]](),
  ) extends pretty.Pretty:
    def ppr =
      val equationsP = equations.map { (r,f) =>
        r.ppr <+> pretty.text("=") <+> f.ppr
      }
      val invariantsP = invariants.toSeq.map { inv =>
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
        if !flow.isInstanceOf[Flow.Pure]
        then
          val (id, deps) = unfoldF(flow, ref, empty)
          if deps.contains(ref) then
            val mubind = graph.add(Op.MuBinder, id)
            val refC = graph.add(Op.Var(ref))
            graph.merge(refC, mubind)
      }

      graph.rebuild()

    /** Turn the crank until we have saturated */
    def crank(): Unit =
      this.boring.fixpoint(options.fix) { () =>
        equivalence.Rewrite.Boring.step(this.boring)
        this.boring.rebuild()
      }
      this.interesting.fixpoint(options.fix) { () =>
        equivalence.Rewrite.Boring.step(this.interesting)
        equivalence.Rewrite.Interesting.step(this.interesting)
        this.interesting.rebuild()
      }

    /** Extract the "interesting" invariants */
    def extract(): Unit =
      def crankX() =
        this.boring.rebuild()
        this.boring.fixpoint(options.fix) { () =>
          equivalence.Rewrite.Boring.step(this.boring)
          this.boring.rebuild()
        }

      val classes = interesting.classes

      // Take equivalence classes of terms that only mention state variables,
      // up to a certain term height. We want to prioritise "simpler"
      // invariants, so a cheap hack is to sort the terms in each equivalence
      // class by the height of the expression, and then sort all of the
      // equivalence classes by the height of the shortest expression.
      // That way, when we go through and try to use them as an invariant,
      // we'll look at some of the shorter terms first.
      //
      // This is a hacky heuristic to prioritise invariants like
      // > x     = x'
      // over the equivalent, but less aesthetically-pleasing
      // > x + 1 = x' + 1
      // but it's OK that it's a hack because it's only aesthetic.
      val terms = classes.map { (klass,nodes) =>
        val ns = takeSimpleTrees(this.boring, classes, klass, options.invariantTermMaxHeight)
        ns.sortBy(_._1.height)
      }.toArray.sortBy(ns => ns.headOption.map(_._1.height).getOrElse(0))

      crankX()

      terms.foreach { ns =>
        ns match
          case (t0, id0) :: rest =>
            var invTerms = List[Tree[Op]]()
            rest.foreach { (t,id) =>
              val k0 = this.boring.find(id0)
              val k  = this.boring.find(id)
              if (k0 != k) {
                this.boring.merge(k0, k)
                invTerms ::= t
                crankX()
              }
            }
            if (invTerms.nonEmpty)
              this.invariants += t0 :: invTerms.reverse
          case Nil =>
      }


    def takeSimpleTrees(g0: EGraph[Op], classes: mutable.SortedMap[EGraph.Id, mutable.HashSet[EGraph.Node[Op]]], klass: EGraph.Id, maxHeight: Int): List[(Tree[Op], EGraph.Id)] =
      val trees = classes(klass).flatMap { n =>
        n.op match
          case Op.Val(_) =>
            val t = Tree(n.op)
            List((t, g0.add(t)))
          // Because we might be inside a "when" context, some variables might
          // be undefined when the clock goes off. The invariants really want
          // to only refer to variables that are defined all the time, so for
          // now only take state variables. My gut feeling is that interesting
          // invariants only refer to state anyway, but maybe there are some
          // interesting invariants where only one side is a state variable?
          case Op.Var(ref)
            if ref.isStateRef =>
            val t = Tree(n.op)
            List((t, g0.add(t)))
          case Op.Prim(p)
           if maxHeight > 0 =>
            val childrenX = n.children.map(takeSimpleTrees(g0, classes, _, maxHeight - 1))
            listCombine(childrenX).map { c => (Tree(n.op, c.map(_._1)), g0.add(n.op, c.map(_._2)*)) }
          // Ignore flow expressions arrow and pre - prefer the named reference.
          case _ => List()
      }
      // Remove duplicates that are already known to be equal by the e-graph
      trees.toList.distinctBy(_._2)

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
    val options: Options,
    val node: Node,
    val layers: mutable.HashMap[Node.Path, Layer] = mutable.HashMap[Node.Path, Layer](),
    val invariants: mutable.ArrayBuffer[Exp] = mutable.ArrayBuffer[Exp](),
  ) extends pretty.Pretty:

    def ppr =
      val layersP = layers.map { (p,l) =>
        val pathP = pretty.ssep(p.map(_.ppr), pretty.space <> pretty.forwslash <> pretty.space)
        pretty.text("Layer") <+> pathP <> pretty.colon <@> pretty.indent(l.ppr)
      }
      val invariantsP = invariants.toSeq.map(_.ppr)
      node.klass.ppr <> pretty.colon <@>
      pretty.indent(pretty.vsep(layersP.toSeq)) <@>
      pretty.indent(pretty.text("Invariant terms:") <@>
        pretty.indent(pretty.vsep(invariantsP)))

    def layer(p: Node.Path): Layer =
      layers.getOrElseUpdate(p, Layer(p, options))

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
            this.appendEGraph(prefix, snLayer.boring, layerX.boring)
            this.appendEGraph(prefix, snLayer.interesting, layerX.interesting)
          }
          snLayers.invariants.foreach { inv =>
            // XXX: why do we add the invariants here? why not put them in the
            // node itself and have them be inherited like regular properties.
            // Then we wouldn't have to re-prove them at every level.
            this.invariants += Compound.substVV(prefix(_), inv)
          }
        }
      }

      // Add a constraint for each equation
      equations.foreach { (path, equationsX) =>
        val layerX = layer(path)
        equationsX.foreach { (ref, flow) =>
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
      // TODO: here, or in assemble, we can sink pure expressions down to lower
      // layers. (It's not so easy to sink streaming expressions though.)
      // This would give the lower layers some more context.

      layers.foreach { (p,l) =>
        l.normalise()
      }


    /** Turn the crank until we have saturated */
    def crank(): Unit =
      layers.foreach { (p,l) =>
        l.crank()
      }

    /** Extract the invariants */
    def extract(): Unit =
      layers.foreach { (p,l) =>
        l.extract()
      }

      val opts = core.node.Check.Options(exposeStateVariables = true)
      val env  = core.node.Check.envOfNode(names.Prefix(), this.node, opts)
      val invs = layers.flatMap { (p, l) =>
        def eqs(trees: List[Tree[Op]]): Exp =
          val exps = trees.map(expOfTree(env, _))
          exps.zip(exps.drop(1)).map { (l,r) =>
            Compound.app(term.prim.Table.Eq, l, r)
          }.reduce { (l,r) =>
            Compound.app(term.prim.Table.And, l, r)
          }

        // If there are multiple init flags, then we include an invariant that
        // they're all equal. We don't use the equivalence class machinery for
        // this because we also use the init flags to deal with invariants that
        // refer to unguarded pres.
        val inits =
          if l.inits.length > 1
          then Some(eqs(l.inits.toList.map(r => Tree(Op.Var(r)))))
          else None

        val rest = l.invariants.map { trees =>
          val inv = eqs(trees)
          // If the invariant refers to a "pre", then it will be undefined on
          // the first step. Rather than trying to figure out whether it's OK,
          // just make the invariant always true on the first step.
          l.inits.headOption.fold(inv) { init =>
            Compound.app(term.prim.Table.Or, Compound.var_(Sort.Bool, init), inv)
          }
        }
        inits ++ rest
      }.toList
      this.invariants ++= invs

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


    /** Append a subnode graph (source) into the destination graph (dest). Any
     * variable references in the subnode graph are prefixed with the prefix. */
    def appendEGraph(prefix: names.Prefix, source: EGraph[Op], dest: EGraph[Op]): Unit =
      // Mapping from e-classes in the source to e-classes in the destination
      val destClass = mutable.HashMap[source.Class, dest.Class]()
      // Both graphs must be canonical because we're going to use equivalence
      // information from both.
      source.rebuild()
      dest.rebuild()
      dest.fixpoint(options.fix) { () =>
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
      }

  def program(nodes: List[Node], options: Options, dump: debug.Options, stage: debug.Stage): names.immutable.RefMap[Layers] =
    val mpNodeLayers = mutable.SortedMap[names.Ref, Layers]()
    nodes.foreach { n =>
      val layers = node(n, mpNodeLayers, options)
      dump.traceP(layers, stage, Some(n.klass.pprString))
      mpNodeLayers += n.klass -> layers
    }
    immutable.SortedMap.from(mpNodeLayers)


  def node(node: Node, mpNodeLayers: names.mutable.RefMap[Layers], options: Options): Layers =
    val layers = Layers(options, node)
    layers.assemble(mpNodeLayers)
    layers.normalise()
    layers.crank()
    layers.extract()
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


  def bindingsOfNode(node: Node): (mutable.HashMap[Node.Path, names.mutable.RefMap[Flow]], mutable.HashMap[Node.Path, names.mutable.ComponentMap[Node.Binding.Subnode]]) =
    val equations = mutable.HashMap[Node.Path, names.mutable.RefMap[Flow]]()
    val subnodes  = mutable.HashMap[Node.Path, names.mutable.ComponentMap[Node.Binding.Subnode]]()

    node.allSubnesteds.foreach { (n,p) =>
      n.bindings.foreach { (c,b) =>
        b match
          case Node.Binding.Equation(_, flow) =>
            val ref = names.Ref.fromComponent(c)
            // We include the internal state variables, because these retain
            // their value when the clock is off inside "when" contexts. If the
            // invariants referred to normal variables inside a "when", the
            // values would be undefined and it wouldn't make sense.
            // Only "pre" and "fby" have state variables.
            val state = flow match
              case Flow.Fby(_, _) | Flow.Pre(_) =>
                List(names.Ref(List(n.context), c) -> Flow.Pure(Exp.Var(flow.sort, ref)))
              case _ => List()
            val binds = (ref -> flow) :: state
            equations.getOrElseUpdate(p, mutable.SortedMap()) ++= binds
          case b: Node.Binding.Subnode =>
            subnodes.getOrElseUpdate(p, mutable.SortedMap()) += (c -> b)
      }
    }
    (equations, subnodes)
