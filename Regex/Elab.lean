import Lean
import Regex.Parser

open Lean Meta PrettyPrinter Elab Term

namespace Regex


run_meta do
  let t ← `(term| re"(ab|c|2|3)")
  let t2 ← `(term| re"a bc+[\wa-z]+c{1,2}(ab(c))*|2")
  -- let t2 ← `(term| r{^(x)$})
  println! "{t2}"
  let f2 ← PrettyPrinter.ppTerm t2
  println! "{f2}"


open Regex.Parser in
@[term_elab Regex.Parser.regex]
def elabRegexp : TermElab := fun stx type? => do
  type?.forM fun type => do
    let ex := Expr.const ``RegEx []
    unless (← isDefEq type ex) do
      throwTypeExcepted ex
  match stx.getKind with
  | ``regex => sorry
  | _ => throwUnsupportedSyntax

structure Context where
  inSet : Bool

structure State where
  stack : Array RegEx

abbrev RegexElabM := ReaderT Context <| StateRefT State CoreM

abbrev RegexElab := Syntax → RegexElabM RegEx

-- open Parser
-- def elabRegex : RegexElab := fun stx => do
--   let kind := stx.getKind
--   unless kind == `regexAtom do
--     throwError "expected syntax of kind `regexAtom"
--   match stx with
--   | `(regexAtom|$a|$b) =>
--     let t := a
--     sorry
--   | _ => sorry
