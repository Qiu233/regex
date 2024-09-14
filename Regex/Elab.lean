import Lean
import Regex.Parser

open Lean Meta PrettyPrinter Elab Term

run_meta do
  let t ← `(term| re"(ab|c)")
  let t2 ← `(term| re"a bc+[\wa-z]+c{1,2}(ab(c))*|2")
  -- let t2 ← `(term| r{^(x)$})
  println! "{t2}"
  let f2 ← PrettyPrinter.ppTerm t2
  println! "{f2}"

inductive RegEx where
  -- TODO

open Regex.Parser in
@[term_elab Regex.Parser.regex]
def elabRegexp : TermElab := fun stx type? => do
  type?.forM fun type => do
    let ex := Expr.const ``RegEx []
    unless (← isDefEq type ex) do
      throwTypeExcepted ex
  match stx with
  | `(regex| re"$[^]?$[$atom?]?$[$]?") =>
    let s := atom?
    sorry
  | _ => throwUnsupportedSyntax
