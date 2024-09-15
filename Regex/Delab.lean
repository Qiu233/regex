import Lean
import Regex.Parser
import Regex.Basic

namespace Regex.Elab
open Lean Meta Elab Term Parser RegEx PrettyPrinter Delaborator SubExpr



def delabRegEx : Delab := do
  let e ← SubExpr.getExpr
  guard <| e.hasFVar && e.hasMVar
  sorry
