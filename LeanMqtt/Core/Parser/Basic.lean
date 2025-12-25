abbrev Parser (α : Type) := StateT (List UInt8) Option α

theorem parser_app_is_run {α} {l : List UInt8} (p : Parser α) :
  p l = p.run l :=
  rfl

def bytesParser (n : Nat) : Parser (List UInt8) := do
  let s ← get
  if s.length < n then
    none
  else
    let chunk := s.take n
    let rest  := s.drop n
    set rest
    return chunk

def bytesParserWithProof (n : Nat) : Parser { l : List UInt8 // l.length = n } := do
  let s ← get
  if h : s.length < n then
    none
  else
    let chunk := s.take n
    let rest  := s.drop n
    set rest
    -- Prove that the chunk has the correct length
    have h_len : chunk.length = n :=
      List.length_take_of_le (Nat.ge_of_not_lt h)
    return ⟨chunk, h_len⟩
