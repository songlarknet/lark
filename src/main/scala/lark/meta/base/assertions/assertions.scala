package lark.meta.base

package object assertions:
  inline def fail(prefix: String, message: String, notes: (String, Any)*): Nothing =
    val msg =
      pretty.text(prefix) <@>
      pretty.string(message)
    val ns = notes.map { case (n,obj) =>
      val pp = pretty.value(obj)
      pretty.text(n) <> pretty.colon <+> pretty.nest(pp)
    }
    throw new java.lang.AssertionError(pretty.layout(msg <@> pretty.vsep(ns)))

  /** An invariant that we should maintain has failed. */
  inline def impossible(message: String, notes: (String, Any)*): Nothing =
    fail("The impossible happened: something is wrong internally.", message, notes : _*)

  /** A strong assumption about the universe has failed */
  inline def implausible(message: String, notes: (String, Any)*): Nothing =
    fail("The implausible happened: something is wrong with the universe.", message, notes : _*)

  /** Something is amiss, but we might be able to continue */
  inline def warn(message: String, notes: (String, Any)*): Unit =
    try
      fail("Warning", message, notes : _*)
    catch
      case e: Exception =>
        e.printStackTrace()
