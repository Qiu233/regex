namespace Regex

inductive Quant where
  | many
  | many1
  | opt
  | range (n : Nat) (m : Nat)
  | rangeLeast (n : Nat)
  | rangeExact (n : Nat)
deriving Inhabited, Repr

inductive Class where
  | w | W
  | s | S
  | d | D
deriving Inhabited, Repr

inductive RegEx where
  | none
  | dot -- .
  | cap -- ^
  | dollar -- $
  | char (c : Char)
  | class (c : Class)
  | set (rs : Array RegEx)
  | setNeg (rs : Array RegEx) -- `set` and `setNeg` can only match one character
  | setRange (low : Char) (high : Char)
  | seq (rs : Array RegEx)
  | group (a : RegEx)
  | quant (e : RegEx) (q : Quant)
deriving Inhabited, Repr


def escapes : Array Char := #[ 'w', 'W', 's', 'S', 'd', 'D', 'n', 'r', 't', 'f', 'v' ]

def metaChars : Array Char := #[ '*', '+', '?', '(', ')', '[', ']', '{', '}', '|' ]

def metaCharsSetElem : Array Char := metaChars.erase ']'

def forbiddenChars : Array Char := #['\r', '\n', '\t', '\x0C', '\x0B'] -- other characters is forbidden by Lean4?
