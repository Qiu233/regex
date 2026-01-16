inductive RegEx.Quant where
  | many
  | many1
  | opt
  | range (n : Nat) (m : Nat)
  | rangeLeast (n : Nat)
  | rangeExact (n : Nat)
deriving Inhabited, Repr

inductive RegEx.Class where
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
  | class (c : RegEx.Class)
  | set (rs : Array RegEx)
  | setNeg (rs : Array RegEx) -- `set` and `setNeg` can only match one character
  | setRange (low : Char) (high : Char)
  | seq (rs : Array RegEx)
  | group (a : RegEx)
  | quant (e : RegEx) (q : RegEx.Quant)
deriving Inhabited, Repr

structure RegEx.Match where
  slice : String.Slice
  groups : Array String.Slice
deriving Inhabited
