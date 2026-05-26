abbrev Parser (α : Type) := StateT (List UInt8) Option α

def Parser.bytes (n : Nat) : Parser (List UInt8) := do
  let s ← get
  if s.length < n then
    none
  else
    let chunk := s.take n
    let rest  := s.drop n
    set rest
    return chunk

def Parser.bytesWithProof (n : Nat) : Parser { l : List UInt8 // l.length = n } := do
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
