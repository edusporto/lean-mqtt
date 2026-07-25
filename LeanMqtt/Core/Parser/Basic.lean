/-!
# Basic Parser

This module defines the core parsing monad used throughout the library to decode
binary data.

Currently, the `Parser` operates over a `List UInt8`. While lists are convenient for
proofs (mostly due to induction), they are inefficient for processing actual binary
streams. In future versions, we would like to migrate this parser to operate over
`Array UInt8` or `ByteArray` for better performance and memory locality.
-/

/--
The `Parser` monad is a state transformer over a byte list, capable of failing
with the `Option` monad. In future versions, we will implement general error
encoding using `Except`.
-/
abbrev Parser (α : Type) := StateT (List UInt8) Option α

/--
Consumes and returns exactly `n` bytes from the parser's state.
Fails if there are fewer than `n` bytes remaining.
-/
def Parser.bytes (n : Nat) : Parser (List UInt8) := do
  let s ← get
  if s.length < n then
    none
  else
    let chunk := s.take n
    let rest  := s.drop n
    set rest
    return chunk

/--
Consumes and returns exactly `n` bytes from the parser's state, returning them
as a dependent type containing a proof of their length. Fails if there are fewer
than `n` bytes remaining.
-/
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
