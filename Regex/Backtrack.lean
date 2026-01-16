import Regex.Basic
import Regex.Elab

structure RegEx.State (input : String) where
  pos : String.ValidPos input
  captures : Array (Option String.Slice) := #[]
deriving Inhabited

abbrev RegExM (s : String) := EStateM Unit (RegEx.State s)

@[always_inline]
instance : EStateM.Backtrackable (RegEx.State s) (RegEx.State s) where
  save := id
  restore _ x := x

@[always_inline]
instance : Alternative (RegExM input) where
  failure := throw ()
  orElse a b := EStateM.orElse' a (b ()) (useFirstEx := false)

namespace RegEx

@[always_inline]
def next : RegExM input Char := do
  let s ← get
  if h : s.pos.IsAtEnd then
    throw ()
  else
    MonadState.set {s with pos := s.pos.next h }
    return s.pos.get h

@[always_inline, specialize]
def shouldFail (x : RegExM input Unit) : RegExM input Unit := do
  let s ← get
  let t ←
    try (some <$> x)
    catch _ => (pure Option.none)
    finally (MonadState.set s)
  match t with
  | .none => return ()
  | .some _ => throw ()

@[always_inline, specialize]
partial def atomic (x : RegExM input Unit) : RegExM input Unit := do
  let s ← get
  try
    x
  catch _ =>
    MonadState.set s
    throw ()

@[always_inline, specialize]
partial def matchManyGreedy (x kont : RegExM input Unit) : RegExM input Unit := do
  let s ← get
  try
    x
    matchManyGreedy x kont
  catch _ =>
    MonadState.set s
    kont

@[always_inline, specialize]
partial def matchOptGreedy (x kont : RegExM input Unit) : RegExM input Unit := do
  let s ← get
  try
    x
  catch _ =>
    MonadState.set s
  kont

variable (input : String) in
partial def run (s : RegEx) (kont : RegExM input Unit) : RegExM input Unit := atomic do
  match s with
  | .none => pure ()
  | .dot =>
    let s ← next
    guard <| s != '\n'
    kont
  | .cap =>
    let s ← get
    if h : s.pos = input.startValidPos then
      pure ()
    else
      let last := s.pos.prev h
      guard <| last.get! == '\n'
    kont
  | .dollar =>
    let s ← get
    guard <| s.pos.IsAtEnd
    kont
  | .char c =>
    let t ← next
    guard <| t == c
    kont
  -- TODO: replace this by more efficient implementations
  | .class .w => run [regex|[a-zA-Z_0-9]] kont
  | .class .W => run [regex|[^a-zA-Z_0-9]] kont
  | .class .s => run [regex|[ \f\n\r\t\v]] kont
  | .class .S => run [regex|[^ \f\n\r\t\v]] kont
  | .class .d => run [regex|[0-9]] kont
  | .class .D => run [regex|[^0-9]] kont
  | .set es =>
    es.map (run · kont) |>.foldl (init := failure) (· <|> ·)
    kont
  | .setNeg es =>
    let s ← get
    if s.pos.IsAtEnd then
      throw ()
    es.map (run · kont) |>.map shouldFail |>.foldl (init := pure ()) (· >>= fun _ => ·)
    _ ← next -- only consume one character
    kont
  | .setRange low high =>
    let t ← next
    guard <| low ≤ t && t ≤ high
    kont
  | .seq es =>
    es.foldr (init := kont) run
  | .group e =>
    let pos := (← get).pos
    let idx := (← get).captures.size
    modify (fun s => {s with captures := s.captures.push Option.none})
    run e kont
    let pos' := (← get).pos
    if h : pos ≤ pos' then
      let str : String.Slice := { str := input, startInclusive := pos, endExclusive := pos', startInclusive_le_endExclusive := h }
      modify (fun s => {s with captures := s.captures.set! idx str})
    else
      panic! "pos > pos'"
  | .quant e q =>
    match q with
    | .many => matchManyGreedy (run e (pure ())) kont
    | .many1 =>
      run e (pure ())
      matchManyGreedy (run e (pure ())) kont
    | .opt => matchOptGreedy (run e (pure ())) kont
    | .range n m =>
      for _ in [:n] do
        run e (pure ())
      let ts := Array.replicate (m - n) e
      ts.foldr (init := kont) fun x acc => matchOptGreedy (run x (pure ())) acc
    | .rangeLeast n =>
      for _ in [:n] do
        run e (pure ())
      matchManyGreedy (run e (pure ())) kont
    | .rangeExact n =>
      for _ in [:n] do
        run e (pure ())
      kont

end RegEx

partial def RegEx.match (r : RegEx) (s : String) : Array RegEx.Match := go s.startValidPos
  where
  go pos :=
    if h : pos = s.endValidPos then
      #[]
    else
      let t : EStateM.Result _ _ _ := r.run s (kont := pure ()) |>.run {pos := pos}
      match t with
      | .error .. => go (pos.next h)
      | .ok _ t =>
        let cs := t.captures.map fun x => x.get!
        let main : String.Slice := if h : pos ≤ t.pos then
            { str := s, startInclusive := pos, endExclusive := t.pos,
                                     startInclusive_le_endExclusive := h }
          else unreachable!
        #[RegEx.Match.mk main cs].append <| go t.pos
