import Lean
import Regex.Basic

open Lean Parser PrettyPrinter Syntax.MonadTraverser

namespace Regex.Parser

/- **DESIGN NOTE**
Our purpose is to find as much as errors with aid of Lean4's compiler.

Whitespaces must be handled manually, because Lean4's infrastructure doesn't care about the spaces between tokens.
This is why there are many hand-written `ParserFn`s rather than `ParserDescr`s.

To avoid too much memory being taken by characters, we make them each a `Syntax.atom` rather than `Syntax.node`.

All these concerns will make the parser much more tedious.

The following is syntax rules for regex.
The uppercase-leading nodes are tagged with their own `SyntaxNodeKind`.
There's no antiquot due to recursion, and cannot be implemented with syntax category (whitespaces sensitive).
-/

/-

  terminals := { atomChar, setChar, num }

  Atom → Quantified+ ('|' (Quantified+))*
  Quantified → body quant?

  body → atomChar | Set | Group

  quant → '*' | '+' | '?' | QuantRange
  QuantRange → '{' num (',' num?)? '}'

  Group → '(' Atom ')'

  Set → '[' SetElem* ']'
  Set → '[^' SetElem* ']'

  SetElem → setChar ('-' setChar)

-/


-- set_option trace.Elab.definition true

def escapes : Array Char := #[ 'w', 'W', 's', 'S', 'd', 'D', 'n', 'r', 't' ]
def metaChars : Array Char := #[ '*', '+', '?', '(', ')', '[', ']', '{', '}', '|' ]
def metaCharsSetElem : Array Char := metaChars.erase ']'
def forbiddenChars : Array Char := #['\r', '\n', '\t'] -- other characters is forbidden by Lean4?

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
  if forbiddenChars.contains curr then
    s.mkUnexpectedErrorAt s!"unexpected forbidden character '{curr}'" i
  else if curr == ' ' || curr.isAlpha || curr.isDigit || curr == '_' || curr == '-' ||
     curr == '.' || curr == '^' || curr == '$' || curr == '\"' then
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
private def ch_dquote : Parser := rawCh '"'
private def ch_vbar : Parser := rawCh '|'

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
    andthenFn ch_parenL.fn (andthenFn regexAtomFn ch_parenR.fn) c s
  else
    s.mkErrorAt "'('" i

end

def regexAtom : Parser where
  fn := regexAtomFn
  info := mkAtomicInfo "regexAtom"

def regexAtomQuantified : Parser where
  fn := regexAtomQuantifiedFn
  info := mkAtomicInfo "regexAtomQuantified"

def regexAtomGrouped : Parser where
  fn := regexAtomGroupedFn
  info := mkAtomicInfo "regexAtomGrouped"

open Parenthesizer Formatter in
mutual

@[combinator_parenthesizer regexAtomQuantified]
partial def regexAtomQuantified.parenthesizer : Parenthesizer := do checkKind `regexAtomQuantified; visitToken
@[combinator_parenthesizer regexAtom]
partial def regexAtom.parenthesizer : Parenthesizer := do checkKind `regexAtom; visitToken
@[combinator_parenthesizer regexAtomGrouped]
partial def regexAtomGrouped.parenthesizer : Parenthesizer := do checkKind `regexAtomGrouped; visitToken

@[combinator_formatter regexAtomQuantified]
partial def regexAtomQuantified.formatter : Formatter := do
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
    | .node _ `regexAtomGrouped _ => regexAtomGrouped.formatter
    | _ => throwError s!"unsupported {stx}"

@[combinator_formatter regexAtom]
partial def regexAtom.formatter : Formatter := do
  checkKind `regexAtom
  visitArgs do
    sepBy1.formatter (many1.formatter regexAtomQuantified.formatter) "|" (rawCh.formatter '|')

@[combinator_formatter regexAtomGrouped]
partial def regexAtomGrouped.formatter : Formatter := do
  checkKind `regexAtomGrouped
  visitArgs do
    rawCh.formatter ')'
    regexAtom.formatter
    rawCh.formatter '('

end

syntax (name := regex) withPosition("[regex" noWs ch_vbar noWs (regexAtom)? noWs "]") : term
