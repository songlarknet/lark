package lack.meta.base

package object assertions:
  inline def impossible(message: String, notes: (String, Object)*): Nothing =
    val msg =
      pretty.text("The 'impossible' happened:") <@>
      pretty.string(message)
    val ns = notes.map { case (n,obj) =>
      val pp = obj match
        case pp: pretty.Pretty => pp.ppr
        case _ => pretty.value(obj)
      pretty.text(n) <> pretty.colon <+> pretty.nest(pp)
    }
    throw new java.lang.AssertionError(pretty.layout(msg <@> pretty.vsep(ns)))

