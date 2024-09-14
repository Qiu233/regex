import Lean

open Lean Parser PrettyPrinter Syntax.MonadTraverser

namespace Regex.Parser

-- set_option trace.Elab.definition true

def escapes : Array Char := #[ 'w', 'W', 's', 'S', 'd', 'D', 'n', 'r', 't' ]
def metaChars : Array Char := #[ '*', '+', '?', '^', '$', '(', ')', '[', ']', '{', '}' ]
def metaCharsSetElem : Array Char := metaChars.erase ']'

partial def regexCharEscapedAux : ParserFn := rawFn (trailingWs := false) fun c s =>
  let input := c.input
  let pos   := s.pos
  if input.get pos != '\\' then
    s.mkError "'regexCharEscapedAux' must be called on '\\'"
  else
    let s := s.next input pos
    let i := s.pos
    if h : input.atEnd i then s.mkEOIError
    else
      let curr := input.get i
      if escapes.contains curr then
        s.next' input i h
      else
        s.mkUnexpectedErrorAt "invalid escape" i

partial def regexCharFn (meta : Bool) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  let curr  := input.get i
  if curr == ' ' || curr.isAlpha || curr.isDigit || curr == '_' || curr == '-' || curr == '.' then
    rawFn (satisfyFn (fun _ => true) "") false c s
  else if !meta && metaCharsSetElem.contains curr then
    rawFn (satisfyFn (fun _ => true) "") false c s
  else if curr == '\\' then
    regexCharEscapedAux c s
  else if meta && metaChars.contains curr then
    s.mkUnexpectedErrorAt s!"unexpected meta character '{curr}'" i
  else
    s.mkUnexpectedErrorAt s!"unexpected character '{curr}'" i

/-- no node -/
def regexSetChar : Parser where
  fn := regexCharFn false
  info := mkAtomicInfo "regexSetChar"

/-- no node -/
def regexAtomChar : Parser where
  fn := regexCharFn true
  info := mkAtomicInfo "regexAtomChar"

open Parenthesizer in
@[combinator_parenthesizer regexAtomChar, combinator_parenthesizer regexSetChar]
def regexChar.parenthesizer : Parenthesizer := do
  checkKind `regexAtomChar
  visitToken

open Formatter in
@[combinator_formatter regexAtomChar, combinator_formatter regexSetChar]
def regexChar.formatter : Formatter := do
  let stx ← getCur
  match stx with
  | .atom info s =>
    modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
    goLeft
  | _ => throwError s!"not an regex character: {← getCur}"

private def ch_bar : Parser := rawCh '-'
private def ch_mul : Parser := rawCh '*'
private def ch_add : Parser := rawCh '+'
private def ch_opt : Parser := rawCh '?'
private def ch_parenL : Parser := rawCh '('
private def ch_parenR : Parser := rawCh ')'
private def ch_braceL : Parser := rawCh '{'
private def ch_braceR : Parser := rawCh '}'
private def ch_bracketL : Parser := rawCh '['
private def ch_bracketR : Parser := rawCh ']'
private def ch_comma : Parser := rawCh ','
private def ch_sharp : Parser := rawCh '#'
private def ch_r : Parser := rawCh 'r'
private def ch_e : Parser := rawCh 'e'
private def ch_cap : Parser := rawCh '^'
private def ch_dollar : Parser := rawCh '$'
private def ch_dquote : Parser := rawCh '"'

def regexSetElem : Parser := node `regexSetElem <| regexSetChar >> atomic (optional (ch_bar >> regexSetChar))

open Parenthesizer in
@[combinator_parenthesizer regexSetElem]
def regexSetElem.parenthesizer : Parenthesizer := do checkKind `regexSetElem; visitToken

open Formatter in
@[combinator_formatter regexSetElem]
partial def regexSetElem.formatter : Formatter := do
  checkKind `regexSetElem
  visitArgs do
    if !(← getCur).isNone then
      visitArgs do
        regexChar.formatter
        visitAtom Name.anonymous
    else
      goLeft
    regexChar.formatter

def regexSetPos := ("[" >> many regexSetElem >> "]")
def regexSetNeg := ("[^" >> many regexSetElem >> "]")

def regexSet : Parser := node `regexSet (regexSetPos <|> regexSetNeg)

open Parenthesizer in
@[combinator_parenthesizer regexSet]
def regexSet.parenthesizer : Parenthesizer := do checkKind `regexSet; visitToken

open Formatter in
@[combinator_formatter regexSet]
partial def regexSet.formatter : Formatter := do
  checkKind `regexSet
  visitArgs do
    visitAtom Name.anonymous
    many.formatter regexSetElem.formatter
    visitAtom Name.anonymous

@[run_parser_attribute_hooks]
def regexQuant : Parser := ch_mul <|> ch_add <|> ch_opt
  <|> node `regexQuantRange (ch_braceL >> numLit >> optional (ch_comma >> optional numLit) >> ch_braceR)

mutual

partial def regexAtomFn : ParserFn := nodeFn `regexAtom <| sepBy1Fn false (sep := chFn '|') (many1Fn regexAtomQuantifiedFn)

partial def regexAtomQuantifiedFn := nodeFn `regexAtomQuantified <| andthenFn regexAtomBodyFn regexAtomQuantifierOptFn
  where
    regexAtomQuantifierOptFn := optionalFn regexQuant.fn
    regexAtomBodyFn := orelseFn regexAtomChar.fn <| orelseFn regexSet.fn <| regexAtomGroupedFn

partial def regexAtomGroupedFn := nodeFn `regexAtomGrouped fun c s =>
  let i := s.pos
  let curr := c.input.get i
  if curr == '(' then
    andthenFn ch_parenL.fn (andthenFn (manyFn regexAtomFn) ch_parenR.fn) c s
  else
    s.mkErrorAt "'('" i

end

def regexAtomNoAntiquot : Parser where
  fn := regexAtomFn
  info := mkAtomicInfo "regexAtom"

def regexAtomQuantifiedNoAntiquot : Parser where
  fn := regexAtomQuantifiedFn
  info := mkAtomicInfo "regexAtomQuantified"

def regexAtomGroupedNoAntiquot : Parser where
  fn := regexAtomGroupedFn
  info := mkAtomicInfo "regexAtomGrouped"

open Parenthesizer Formatter in
mutual

@[combinator_parenthesizer regexAtomQuantifiedNoAntiquot]
partial def regexAtomQuantifiedNoAntiquot.parenthesizer : Parenthesizer := do checkKind `regexAtomQuantified; visitToken
@[combinator_parenthesizer regexAtomNoAntiquot]
partial def regexAtomNoAntiquot.parenthesizer : Parenthesizer := do checkKind `regexAtom; visitToken
@[combinator_parenthesizer regexAtomGroupedNoAntiquot]
partial def regexAtomGroupedNoAntiquot.parenthesizer : Parenthesizer := do checkKind `regexAtomGrouped; visitToken

@[combinator_formatter regexAtomQuantifiedNoAntiquot]
partial def regexAtomQuantifiedNoAntiquot.formatter : Formatter := do
  checkKind `regexAtomQuantified
  visitArgs do
    if (← getCur).isNone then
      goLeft
    else
      visitArgs regexQuant.formatter
    let stx ← getCur
    match stx with
    | .atom i s => regexChar.formatter
    | .node _ `regexSet _ => regexSet.formatter
    | .node _ `regexAtomGrouped _ => regexAtomGroupedNoAntiquot.formatter
    | _ => throwError s!"unsupported {stx}"

@[combinator_formatter regexAtomNoAntiquot]
partial def regexAtomNoAntiquot.formatter : Formatter := do
  checkKind `regexAtom
  visitArgs do
    sepBy1.formatter (many1.formatter regexAtomQuantifiedNoAntiquot.formatter) "|" (rawCh.formatter '|')

@[combinator_formatter regexAtomGroupedNoAntiquot]
partial def regexAtomGroupedNoAntiquot.formatter : Formatter := do
  checkKind `regexAtomGrouped
  visitArgs do
    rawCh.formatter ')'
    many.formatter regexAtomNoAntiquot.formatter
    rawCh.formatter '('

@[run_parser_attribute_hooks]
partial def regexAtomQuantified : Parser :=
  withAntiquot (mkAntiquot "regexAtomQuantified" `regexAtomQuantified) regexAtomQuantifiedNoAntiquot

@[run_parser_attribute_hooks]
partial def regexAtom : Parser :=
  withAntiquot (mkAntiquot "regexAtom" `regexAtom) regexAtomNoAntiquot

@[run_parser_attribute_hooks]
partial def regexAtomGrouped : Parser :=
  withAntiquot (mkAntiquot "regexAtomGrouped" `regexAtomGrouped) regexAtomGroupedNoAntiquot

end

syntax (name := regex) "re" noWs ch_dquote noWs (ch_cap)? (regexAtom)? (ch_dollar)? noWs ch_dquote : term
