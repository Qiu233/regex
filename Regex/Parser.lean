import Lean
import Regex.Basic

open Lean Parser PrettyPrinter Syntax.MonadTraverser

namespace Regex.Parser

-- set_option trace.Elab.definition true

def escapes : Array Char := #[
  'w', 'W', 's', 'S', 'd', 'D', 'n', 'r', 't', 'f', 'v', 'b', 'e', 'a', -- TODO: how about '\c'?
  '.', '*', '+', '?', '(', ')', '[', ']', '{', '}',
  '|', '^', '$', '\\'
  ]
def metaChars : Array Char := #[
  '.', '*', '+', '?', '(', ')', '[', ']', '{', '}',
  '|', '^', '$', '\\' ]
def metaCharsSetElem : Array Char := #[
  '.', '*', '+', '?', '(', ')', '[', '{', '}',
  '|', '$' ]
def forbiddenChars : Array Char := #['\r', '\n', '\t', '\x0C', '\x0B'] -- other characters is forbidden by Lean4?

private def is_hex : Char → Bool := fun c =>
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

partial def regexCharEscapedAux : ParserFn := rawFn (trailingWs := false) fun c s =>
  let pos   := s.pos
  if c.get pos != '\\' then
    s.mkError "'regexCharEscapedAux' must be called on '\\'"
  else
    let s := s.next c pos
    let i := s.pos
    if h : c.atEnd i then s.mkEOIError
    else
      let curr := c.get i
      if escapes.contains curr then
        s.next' c i h
      else if curr == 'x' then
        let s := s.next' c i h
        let i := s.pos
        if h : c.atEnd i then s.mkEOIError else
        let a := c.get' i h
        if !is_hex a then s.mkUnexpectedError "hex digit" else
        let s := s.next' c i h
        let j := s.pos
        if h : c.atEnd j then s.mkEOIError else
        let b := c.get' j h
        if !is_hex b then s.mkUnexpectedError "hex digit" else
        s.next' c j h
      else if curr == 'u' then
        let s := s.next' c i h

        let i := s.pos
        if h : c.atEnd i then s.mkEOIError else
        if !is_hex (c.get' i h) then s.mkUnexpectedError "hex digit" else
        let s := s.next' c i h

        let i := s.pos
        if h : c.atEnd i then s.mkEOIError else
        if !is_hex (c.get' i h) then s.mkUnexpectedError "hex digit" else
        let s := s.next' c i h

        let i := s.pos
        if h : c.atEnd i then s.mkEOIError else
        if !is_hex (c.get' i h) then s.mkUnexpectedError "hex digit" else
        let s := s.next' c i h

        let j := s.pos
        if h : c.atEnd j then s.mkEOIError else
        if !is_hex (c.get' j h) then s.mkUnexpectedError "hex digit" else
        let s := s.next' c j h

        let k := s.pos
        if h : c.atEnd k then s.mkEOIError else
        if !is_hex (c.get' k h) then s.mkUnexpectedError "hex digit" else
        let s := s.next' c k h

        let l := s.pos
        if h : c.atEnd l then s.mkEOIError else
        if !is_hex (c.get' l h) then s.mkUnexpectedError "hex digit" else
        s.next' c l h
      else
        s.mkUnexpectedErrorAt "invalid escape" i

partial def regexCharFn (meta_ : Bool) : ParserFn := fun c s =>
  let i     := s.pos
  let curr  := c.get i
  if forbiddenChars.contains curr then
    s.mkUnexpectedErrorAt s!"unexpected forbidden character '{curr}'" i
  else if curr == ' ' || curr.isAlpha || curr.isDigit || curr == '_' || curr == '-' ||
    curr matches '.' | '^' | '$' | '\"' | '<' | '>' | '#' | '%' | ',' |
      '/' | '\'' | '!' | '&' | '`' | '~' | '@'
    then
    rawFn (satisfyFn (fun _ => true) "") false c s
  else if !meta_ && metaCharsSetElem.contains curr then
    rawFn (satisfyFn (fun _ => true) "") false c s
  else if curr == '\\' then
    regexCharEscapedAux c s
  else if meta_ && metaChars.contains curr then
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
  visitToken

open Formatter in
@[combinator_formatter regexAtomChar, combinator_formatter regexSetChar]
def regexChar.formatter : Formatter := do
  let stx ← getCur
  match stx with
  | .atom _ s =>
    modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
    goLeft
  | _ => throwError s!"not an regex character: {← getCur}"

run_meta do
  modifyEnv (addSyntaxNodeKind (k := `Regex.Parser.regexSetElem))
  modifyEnv (addSyntaxNodeKind (k := `Regex.Parser.regexSet))
  modifyEnv (addSyntaxNodeKind (k := `Regex.Parser.regexQuantRange))

@[run_parser_attribute_hooks]
def regexSetElem : Parser := leading_parser regexSetChar >> atomic (optional (rawCh '-' >> regexSetChar))

def regexSetPos := atomic (rawCh '[' >> many regexSetElem >> rawCh ']')

def regexSetNeg := atomic (group (rawCh '[' >> rawCh '^') >> many regexSetElem >> rawCh ']')

@[run_parser_attribute_hooks]
def regexSet : Parser := leading_parser (regexSetNeg <|> regexSetPos)

@[run_parser_attribute_hooks]
def regexQuantRange : Parser := leading_parser rawCh '{' >> numLit >> optional (rawCh ',' >> optional numLit) >> rawCh '}'

@[run_parser_attribute_hooks]
def regexQuant : Parser := rawCh '*' <|> rawCh '+' <|> rawCh '?'
  <|> regexQuantRange

/-!
It is very unfortunate that we cannot handle the recursion here by `categoryParser`,
  as `prattParser` uses hard-coded `tokenFn` and `peekToken` to decide which parser to call,
  which breaks parsing of the immediate space character after `|`.
-/

run_meta do
  modifyEnv (addSyntaxNodeKind (k := `Regex.Parser.regexAtom))
  modifyEnv (addSyntaxNodeKind (k := `Regex.Parser.regexAtomQuantified))
  modifyEnv (addSyntaxNodeKind (k := `Regex.Parser.regexAtomGrouped))

mutual

partial def regexAtomFn : ParserFn := nodeFn `Regex.Parser.regexAtom <| sepBy1Fn false (sep := chFn '|') (many1Fn regexAtomQuantifiedFn)

partial def regexAtomQuantifiedFn := nodeFn `Regex.Parser.regexAtomQuantified <| andthenFn regexAtomBodyFn regexAtomQuantifierOptFn
  where
    regexAtomQuantifierOptFn := optionalFn regexQuant.fn
    regexAtomBodyFn := orelseFn regexAtomChar.fn <| orelseFn regexSet.fn <| regexAtomGroupedFn

partial def regexAtomGroupedFn := nodeFn `Regex.Parser.regexAtomGrouped fun c s =>
  let i := s.pos
  let curr := c.get i
  if curr == '(' then
    andthenFn (chFn '(') (andthenFn regexAtomFn (chFn ')')) c s
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
partial def regexAtomQuantified.parenthesizer : Parenthesizer := do
  checkKind `Regex.Parser.regexAtomQuantified
  visitArgs do
    if (← getCur).isNone then
      goLeft
    else
      visitArgs regexQuant.parenthesizer
    let stx ← getCur
    match stx with
    | .atom .. => regexChar.parenthesizer
    | .node _ `Regex.Parser.regexSet _ => regexSet.parenthesizer
    | .node _ `Regex.Parser.regexAtomGrouped _ => regexAtomGrouped.parenthesizer
    | _ => throwError s!"unsupported {stx}"

@[combinator_parenthesizer regexAtom]
partial def regexAtom.parenthesizer : Parenthesizer := do
  checkKind ``Regex.Parser.regexAtom
  visitArgs do
    sepBy1.parenthesizer (many1.parenthesizer regexAtomQuantified.parenthesizer) "|" (rawCh.parenthesizer '|')

@[combinator_parenthesizer regexAtomGrouped]
partial def regexAtomGrouped.parenthesizer : Parenthesizer := do
  checkKind ``Regex.Parser.regexAtomGrouped
  visitArgs do
    rawCh.parenthesizer ')'
    regexAtom.parenthesizer
    rawCh.parenthesizer '('

@[combinator_formatter regexAtomQuantified]
partial def regexAtomQuantified.formatter : Formatter := do
  checkKind ``Regex.Parser.regexAtomQuantified
  visitArgs do
    if (← getCur).isNone then
      goLeft
    else
      visitArgs regexQuant.formatter
    let stx ← getCur
    match stx with
    | .atom .. => regexChar.formatter
    | .node _ `Regex.Parser.regexSet _ => regexSet.formatter
    | .node _ `Regex.Parser.regexAtomGrouped _ => regexAtomGrouped.formatter
    | _ => throwError s!"unsupported {stx}"

@[combinator_formatter regexAtom]
partial def regexAtom.formatter : Formatter := do
  checkKind ``Regex.Parser.regexAtom
  visitArgs do
    sepBy1.formatter (many1.formatter regexAtomQuantified.formatter) "|" (rawCh.formatter '|')

@[combinator_formatter regexAtomGrouped]
partial def regexAtomGrouped.formatter : Formatter := do
  checkKind ``Regex.Parser.regexAtomGrouped
  visitArgs do
    rawCh.formatter ')'
    regexAtom.formatter
    rawCh.formatter '('

end

syntax:max (name := regex) withPosition("[regex|" noWs noWs (regexAtom)? noWs "]") : term
