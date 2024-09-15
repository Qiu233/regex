namespace Regex

/- **DESIGN NOTE**
The following types serve as AST but not what to be run effectively.
-/

inductive Quant where
  | many
  | many1
  | opt
  | range (n : Nat) (m : Nat)
  | rangeLeast (n : Nat)
  | rangeExact (n : Nat)
deriving Inhabited, Repr

inductive Fuzzy where
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
  | fuzzy (c : Fuzzy)
  | or (rs : Array RegEx) -- α|β
  | set (rs : Array RegEx) --
  | setRange (low : Char) (high : Char)
  | setNeg (rs : Array RegEx)
  | seq (rs : Array RegEx)
  | group (a : RegEx)
  | quant (e : RegEx) (q : Quant)
deriving Inhabited, Repr
