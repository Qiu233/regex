
inductive Quant where
  | many
  | many1
  | opt
  | range (n : Nat) (m : Nat)
  | rangeLeast (n : Nat)
  | rangeExact (n : Nat)

inductive Fuzzy where
  | w | W
  | s | S
  | d | D

inductive RegEx where
  | none
  | dot -- .
  | cap -- ^
  | dollar -- $
  | char (c : Char)
  | fuzzy (c : Fuzzy)
  | set (rs : Array RegEx)
  | seq (rs : Array RegEx)
  | or (a b : RegEx)
  | group (a : RegEx)
  | quant (e : RegEx) (q : Quant)
