/- **DESIGN NOTE**
The following types serve as AST but not what to be run effectively.
-/

inductive RegEx.Quant where
  | many
  | many1
  | opt
  | range (n : Nat) (m : Nat)
  | rangeLeast (n : Nat)
  | rangeExact (n : Nat)
deriving Inhabited, Repr

inductive RegEx.Fuzzy where
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
  | fuzzy (c : RegEx.Fuzzy)
  | set (rs : Array RegEx) --
  | setRange (low : Char) (high : Char)
  | setNeg (rs : Array RegEx)
  | seq (rs : Array RegEx)
  | group (a : RegEx)
  | quant (e : RegEx) (q : RegEx.Quant)
deriving Inhabited, Repr
