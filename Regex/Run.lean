import Regex.Basic
import Regex.Elab

structure RegEx.Context where
  input : String
deriving Inhabited, Repr

structure RegEx.State where
  pos : String.Pos := 0
  captures : Array (Option Substring) := #[]
deriving Inhabited, Repr

abbrev RegExM := ReaderT RegEx.Context <| StateT RegEx.State <| ExceptT Unit Id

instance : Alternative RegExM where
  failure := throw ()
  orElse a b := fun c s => do
    let v := a c s
    match v with
    | .ok v => .ok v
    | .error _ => b () c s

namespace RegEx

def next : RegExM Char := fun c s =>
  if h : c.input.atEnd s.pos then
    throw ()
  else
    .ok (c.input.get' s.pos h, {s with pos := c.input.next' s.pos h })

def shouldFail (x : RegExM Unit) : RegExM Unit := do
  let s ← get
  let t ←
    try (some <$> x)
    catch _ => (pure Option.none)
    finally (MonadState.set s)
  match t with
  | .none => return ()
  | .some _ => throw ()

partial def matchMany (x : RegExM Unit) : RegExM Unit := do
  let s ← get
  try
    x
    matchMany x
  catch _ =>
    MonadState.set s

partial def matchOpt (x : RegExM Unit) : RegExM Unit := do
  let s ← get
  try
    x
  catch _ =>
    MonadState.set s

partial def atomic (x : RegExM Unit) : RegExM Unit := do
  let s ← get
  try
    x
  catch _ =>
    MonadState.set s
    throw ()

partial def run (s : RegEx) : RegExM Unit := do
  match s with
  | .none => throw ()
  | .dot => _ ← next
  | .cap =>
    let s ← get
    guard <| s.pos == 0
  | .dollar =>
    let c ← read
    let s ← get
    guard <| s.pos == c.input.endPos
  | .char c =>
    let t ← next
    guard <| t == c
  -- TODO: replace this by more efficient implementations
  | .fuzzy .w => run ([regex|[a-zA-Z_0-9]])
  | .fuzzy .W => run ([regex|[^a-zA-Z_0-9]])
  | .fuzzy .s => run ([regex|[ \f\n\r\t\v]])
  | .fuzzy .S => run ([regex|[^ \f\n\r\t\v]])
  | .fuzzy .d => run ([regex|[0-9]])
  | .fuzzy .D => run ([regex|[^0-9]])
  | .set es =>
    let actions := es.map run |>.foldl (init := failure) (· <|> ·)
    atomic actions
  | .setNeg es =>
    let c ← read
    let s ← get
    if c.input.atEnd s.pos then
      throw ()
    let actions := es.map run |>.map shouldFail |>.foldl (init := pure ()) (· >>= fun _ => ·)
    atomic actions
    _ ← next -- only consume one character
  | .setRange low high =>
    let t ← next
    guard <| low ≤ t && t ≤ high
  | .seq es =>
    let actions := es.map run |>.foldl (init := pure ()) (· >>= fun _ => ·)
    atomic actions
  | .group e =>
    atomic do
      let pos := (← get).pos
      let idx := (← get).captures.size
      modify (fun s => {s with captures := s.captures.push Option.none})
      run e
      let pos' := (← get).pos
      let str := Substring.mk (← read).input pos pos'
      modify (fun s => {s with captures := s.captures.set! idx str})
  | .quant e q =>
    match q with
    | .many => matchMany (run e)
    | .many1 => run e; matchMany (run e)
    | .opt => matchOpt (run e)
    | .range n m =>
      atomic do
        for _ in [:n] do
          run e
        for _ in [:(m - n)] do
          matchOpt (run e)
    | .rangeLeast n =>
      atomic do
        for _ in [:n] do
          run e
        matchMany (run e)
    | .rangeExact n =>
      atomic do
        for _ in [:n] do
          run e

end RegEx

partial def RegEx.match (r : RegEx) (s : String) : Array <| Array Substring := go 0
  where
  go pos :=
    if h : s.atEnd pos then
      #[]
    else
      let t : Except _ _ := r.run {input := s} {pos := pos}
      match t with
      | .error _ => go (s.next' pos h)
      | .ok ((), t) =>
        let cs := t.captures.map fun x => x.get!
        #[cs].append <| go t.pos

#eval [regex|ab|c|2|3]
#eval [regex|[a-zA-Z_0-9]]
#eval [regex|[^a-zA-Z_0-9]]
#eval [regex|[ \f\n\r\t\v]]
#eval [regex|[^ \f\n\r\t\v]]
#eval [regex|[0-9]]
#eval [regex|[^0-9]]

#eval RegEx.match ([regex|(a(bc))(d|a)|(\d{3,4})]) "abcaabcd12345"
