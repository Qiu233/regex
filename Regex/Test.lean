import Regex.Backtrack

instance : ToString (String.Slice) where
  toString x := s!"{String.fromUTF8! (ByteArray.mk <| x.bytes.toArray)}"

instance : ToString (RegEx.Match) where
  toString x := s!"\{ slice := {x.slice}, groups := {x.groups}}"

#eval [regex|]

#eval [regex|<.+>].match "<abc>abc<h>"
