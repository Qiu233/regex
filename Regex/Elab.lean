import Lean
import Regex.Parser

namespace Regex.Elab
open Lean Meta Elab Term Parser RegEx

structure Context where
  inSet : Bool := false

structure State where

abbrev RegexElabM := ReaderT Context <| StateRefT State MetaM

private def noneExpr := Expr.const ``RegEx.none []
private def typeExpr := Expr.const ``RegEx []

private def isInSet : RegexElabM Bool := fun c _ => return c.inSet

private def mkCharLit (c : Char) :=
  (Expr.app (Expr.const ``Char.ofNat []) (mkRawNatLit c.toNat))

private def mkChar (c : Char) :=
  Expr.app (Expr.const ``RegEx.char []) (mkCharLit c)

private def escape? : String → Option Char
  | "\\r" => '\r'
  | "\\n" => '\n'
  | "\\t" => '\t'
  | "\\f" => '\x0C'
  | "\\v" => '\x0B'
  | _ => none

private def fuzzy? : String → Option Expr
  | "\\w" => mkFuzzy ``Fuzzy.w
  | "\\W" => mkFuzzy ``Fuzzy.W
  | "\\s" => mkFuzzy ``Fuzzy.s
  | "\\S" => mkFuzzy ``Fuzzy.S
  | "\\d" => mkFuzzy ``Fuzzy.d
  | "\\D" => mkFuzzy ``Fuzzy.D
  | _ => none
  where
    mkFuzzy x := Expr.app (Expr.const ``RegEx.fuzzy []) (Expr.const x [])

mutual

private partial def elabRegexAtom : TSyntax `regexAtom → RegexElabM Expr := fun stx => do
  let components := stx.raw[0].getSepArgs
  let ors ← components.mapM fun qs => withRef qs do
    let qs := TSyntaxArray.mk (ks := `regexAtomQuantified) qs.getArgs
    let ands ← qs.mapM fun (q : TSyntax `regexAtomQuantified) => withRef q (elabRegexQuantified q)
    if ands.size == 1 then
      return ands[0]!
    let arr ← mkArrayLit typeExpr ands.toList
    return Expr.app (Expr.const ``RegEx.seq []) arr
  if ors.size == 1 then
    return ors[0]!
  let arr ← mkArrayLit typeExpr ors.toList
  return Expr.app (Expr.const ``RegEx.set []) arr

private partial def elabRegexChar : Syntax → RegexElabM (Expr × Option Char) := fun stx => do
  let .atom _ s := stx | unreachable!
  if !(← isInSet) then
    if s == "." then
      return (Expr.const ``RegEx.dot [], none)
    else if s == "^" then
      return (Expr.const ``RegEx.cap [], none)
    else if s == "$" then
      return (Expr.const ``RegEx.dollar [], none)
  if let some c := escape? s then
    return (mkChar c, some c)
  if let some f := fuzzy? s then
    return (f, none)
  unless s.length == 1 do
    panic! s!"{s} is not handled"
  let c := s.toList[0]!
  return (mkChar c, some c)

private partial def elabRegexSetElem : TSyntax `regexSetElem → RegexElabM Expr := fun stx => do
  let char := stx.raw[0]
  let suffix := stx.raw[1]
  if suffix.isNone then
    Prod.fst <$> elabRegexChar char
  else
    let (_, some lowC) ← elabRegexChar char
      | throwErrorAt char "invalid character class"
    let (_, some highC) ← elabRegexChar suffix[1]!
      | throwErrorAt suffix[1]! "invalid character class"
    if lowC > highC then
      throwError "invalid character class"
    return Expr.app (Expr.app (Expr.const ``RegEx.setRange []) (mkCharLit lowC)) (mkCharLit highC)

private partial def elabRegexBody : Syntax → RegexElabM Expr := fun body => do
  match body with
  | .atom .. =>
    let t ← withRef body <| Prod.fst <$> elabRegexChar body
    pure t
  | .node _ `regexSet args =>
    let head := args[0]!
    let setElems : TSyntaxArray `regexSetElem := TSyntaxArray.mk args[1]!.getArgs
    let setElems ← withTheReader Context ({· with inSet := true}) do
      setElems.mapM fun elem => withRef elem.raw <| elabRegexSetElem elem
    let arr ← mkArrayLit typeExpr setElems.toList
    match head with
    | .atom _ "[" => pure <| Expr.app (Expr.const ``RegEx.set []) arr
    | .node _ `group #[.atom _ "[", .atom _ "^"] => pure <| Expr.app (Expr.const ``RegEx.setNeg []) arr
    | _ => withRef head throwUnsupportedSyntax
  | .node _ `regexAtomGrouped args =>
    let atom := args[1]!
    unless atom.getKind == `regexAtom do
      withRef atom throwUnsupportedSyntax
    let atom : TSyntax `regexAtom := TSyntax.mk atom
    let e ← withRef atom <| elabRegexAtom atom
    pure <| Expr.app (Expr.const ``RegEx.group []) e
  | _ => withRef body throwUnsupportedSyntax

private partial def elabRegexQuant : Syntax → RegexElabM Expr := fun stx => do
  match stx with
  | .atom _ "*" => return Expr.const ``Quant.many []
  | .atom _ "+" => return Expr.const ``Quant.many1 []
  | .atom _ "?" => return Expr.const ``Quant.opt []
  | .node _ `regexQuantRange args =>
    let low := args[1]!
    let some low := low.isNatLit? | withRef low throwUnsupportedSyntax
    let suffix? := args[2]!
    if suffix?.isNone then
      return Expr.app (Expr.const ``Quant.rangeExact []) (mkRawNatLit low)
    let comma := suffix?[0]!
    unless comma matches .atom _ "," do
      withRef comma throwUnsupportedSyntax
    let high? := suffix?[1]!
    if high?.isNone then
      return Expr.app (Expr.const ``Quant.rangeLeast []) (mkRawNatLit low)
    let some high := high?[0].isNatLit? | withRef high? throwUnsupportedSyntax
    return Expr.app (Expr.app (Expr.const ``Quant.range []) (mkRawNatLit low)) (mkRawNatLit high)
  | _ => withRef stx throwUnsupportedSyntax

private partial def elabRegexQuantified : TSyntax `regexAtomQuantified → RegexElabM Expr := fun stx => do
  unless stx.raw.getKind == `regexAtomQuantified do
    throwUnsupportedSyntax
  let body := stx.raw[0]
  let quant? := stx.raw[1]
  let body ← elabRegexBody body
  if quant?.isNone then
    return body
  else
    let q ← elabRegexQuant quant?[0]!
    return Expr.app (Expr.app (Expr.const ``RegEx.quant []) body) q

end

@[term_elab Regex.Parser.regex]
def elabRegex : TermElab := fun stx type? => do
  if stx.hasMissing then
    throwError "syntax cannot contains missing"
  type?.forM fun type => do
    let ex := Expr.const ``RegEx []
    unless (← isDefEq type ex) do
      throwTypeExcepted ex
  unless stx.getKind == ``regex do
    throwUnsupportedSyntax
  let atom? := stx[2]
  if atom?.isNone then
    return Expr.const ``RegEx.none []
  let atom := atom?[0]
  let kind := atom.getKind
  unless kind == `regexAtom do
    throwError "expected syntax of kind `regexAtom, but got `{kind}"
  let atom := TSyntax.mk (ks := `regexAtom) atom
  let go := elabRegexAtom atom {}
  go.run' {}

run_meta do
  let t ← `(term| [regex|[^a-zA-Z_0-9]])
  let t2 ← `(term| [regex|a bc+[\wa-z]+c{1,2}(ab(c))*|2])
  println! "{t}"
  let f2 ← PrettyPrinter.ppTerm t
  println! "{f2}"
