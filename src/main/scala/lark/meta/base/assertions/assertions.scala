package lark.meta.base

package object assertions:
  inline def fail(prefix: String, message: String, notes: (String, Object)*): Nothing =
    val msg =
      pretty.text(prefix) <@>
      pretty.string(message)
    val ns = notes.map { case (n,obj) =>
      val pp = obj match
        case pp: pretty.Pretty => pp.ppr
        case pp: pretty.Doc => pp
        case _ => pretty.value(obj)
      pretty.text(n) <> pretty.colon <+> pretty.nest(pp)
    }
    throw new java.lang.AssertionError(pretty.layout(msg <@> pretty.vsep(ns)))

  /** An invariant that we should maintain has failed. */
  inline def impossible(message: String, notes: (String, Object)*): Nothing =
    fail("The impossible happened: something is wrong internally.", message, notes : _*)

  /** A strong assumption about the universe has failed */
  inline def implausible(message: String, notes: (String, Object)*): Nothing =
    fail("The implausible happened: something is wrong with the universe.", message, notes : _*)
