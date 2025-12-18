import Std.Tactic.BVDecide
import Helpers.Proofs

abbrev Parser (α : Type) := StateT (List UInt8) Option α

theorem parser_app_is_run {α} {l : List UInt8} (p : Parser α) :
  p l = p.run l :=
  rfl

def UInt8.serialize (b : UInt8) : List UInt8 :=
  [b]

def UInt8.parser : Parser UInt8 := do
  match (← get) with
  | [] => none
  | b :: rest =>
    set rest
    some b

theorem UInt8.roundtrip (b : UInt8) (rest : List UInt8) :
  UInt8.parser.run (b.serialize ++ rest) = some (b, rest) := by
  simp only [
    UInt8.parser, UInt8.serialize, StateT.run_bind, StateT.run_get,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some
  ]
  split
  · contradiction
  · next b' rest' h =>
    simp only [
      List.cons_append, List.nil_append, List.cons.injEq, StateT.run_bind,
      StateT.run_set, Option.pure_def, StateT.run_monadLift, monadLift_self,
      Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq
    ] at *
    exact ⟨h.left.symm, h.right.symm⟩

def bytesParser (n : Nat) : Parser (List UInt8) := do
  let s ← get
  if s.length < n then
    none
  else
    let chunk := s.take n
    let rest  := s.drop n
    set rest
    return chunk

theorem bytesParser_len (n : Nat) (l inp rest : List UInt8) :
  (bytesParser n).run inp = some (l, rest) → l.length = n := by
  simp [bytesParser]
  split
  · intro h_len
    contradiction
  · next h_len =>
    intro h
    simp at h
    have ⟨h_l, h_rest⟩ := h
    subst h_l
    simp [List.length_take]
    omega

theorem bytesParser_reconstruct (n : Nat) (input : List UInt8) (chunk rest : List UInt8) :
  (bytesParser n).run input = some (chunk, rest) → input = chunk ++ rest := by
  simp [bytesParser]
  split
  · intro; contradiction
  · next h_len =>
    simp
    intro h1 h2
    rw [←h1, ←h2]
    apply Eq.symm
    apply List.take_append_drop n input

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

theorem roundtrip_bytes (l : List UInt8) (rest : List UInt8) :
  (bytesParser l.length).run (l ++ rest) = some (l, rest) := by
  simp [bytesParser]
  split
  · omega
  · simp

theorem roundtrip_bytes_with_proof (l : List UInt8) (rest : List UInt8) :
  (bytesParserWithProof l.length).run (l ++ rest) = some (⟨l, rfl⟩, rest) := by
  simp [bytesParserWithProof]
  split
  · omega
  · simp

theorem bytesParserWithProof_eq_parser_success (n : Nat)
  (l : List UInt8) (inp rest : List UInt8) :
  (bytesParser n).run inp = some (l, rest) →
  ∃ h, (bytesParserWithProof n).run inp = some (⟨l, h⟩, rest) := by
  intro h_simple
  have h_len_parser := bytesParser_len _ _ _ _ h_simple
  simp only [bytesParser, bytesParserWithProof] at *
  simp only [bind_pure_comp, StateT.run_bind, StateT.run_get,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some
  ] at *
  split at h_simple
  · contradiction
  · next h_len =>
    simp only [StateT.run_map, StateT.run_set, Option.pure_def,
      Option.map_eq_map, Option.map_some, Option.some.injEq, Prod.mk.injEq
    ] at h_simple
    simp only [dif_neg h_len]
    simp only [StateT.run_map, StateT.run_set, Option.pure_def,
      Option.map_eq_map, Option.map_some, Option.some.injEq, Prod.mk.injEq,
      Subtype.mk.injEq, exists_and_left, exists_prop
    ]
    rcases h_simple with ⟨h_take, h_drop⟩
    exact ⟨h_take, h_len_parser, h_drop⟩

def UInt16.serialize (n : UInt16) : List UInt8 :=
  let b1 := (n >>> 8).toUInt8
  let b2 := n.toUInt8
  [b1, b2]

def UInt16.parser : Parser UInt16 := do
  let bytes ← bytesParser 2
  match bytes with
  | [b1, b2] => return (b1.toUInt16 <<< 8) ||| b2.toUInt16
  | _ => none

theorem UInt16.parser_len (n : UInt16) :
  n.serialize.length = 2 := by
  simp only [UInt16.serialize, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]

theorem UInt16.roundtrip (n : UInt16) (rest : List UInt8) :
  UInt16.parser.run (n.serialize ++ rest) = some (n, rest) := by
  simp [UInt16.parser]
  rw [←UInt16.parser_len n]
  rw [roundtrip_bytes _ _]
  simp [UInt16.serialize]
  bv_decide

def UInt32.serialize (n : UInt32) : List UInt8 :=
  let b1 := (n >>> 24).toUInt8
  let b2 := (n >>> 16).toUInt8
  let b3 := (n >>> 8).toUInt8
  let b4 := n.toUInt8
  [b1, b2, b3, b4]

def UInt32.parser : Parser UInt32 := do
  let bytes ← bytesParser 4
  match bytes with
  | [b1, b2, b3, b4] =>
    return (b1.toUInt32 <<< 24) |||
           (b2.toUInt32 <<< 16) |||
           (b3.toUInt32 <<< 8)  |||
            b4.toUInt32
  | _ => none

theorem UInt32.parser_len (n : UInt32) :
  n.serialize.length = 4 := by
  simp only [UInt32.serialize, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]

theorem UInt32.roundtrip (n : UInt32) (rest : List UInt8) :
  UInt32.parser.run (n.serialize ++ rest) = some (n, rest) := by
  simp only [UInt32.parser, StateT.run_bind, Option.bind_eq_bind]
  rw [←UInt32.parser_len n]
  rw [roundtrip_bytes _ _]
  simp only [
    UInt32.serialize, Option.bind_some, UInt32.toUInt32_toUInt8, StateT.run_pure,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq, and_true
  ]
  bv_decide

-- Note: we do `s.toUTF.data.toList` instead of `s.toUTF.toList` because
-- the `ByteArray.toList` implementation has fewer theorems relating it
-- to `List`s than `Array.toList`.
def String.serialize (s : String) := s.toUTF8.data.toList

def String.parser (len : Nat) : Parser String := do
  let bytes ← bytesParser len
  let txt := bytes.toByteArray
  if h_valid : txt.IsValidUTF8
    then some (String.fromUTF8 txt h_valid)
    else none

def String.parserWithProof (n : Nat) : Parser { s : String // s.utf8ByteSize = n } := do
  let ⟨bytes, h_len⟩ ← bytesParserWithProof n
  let txt := bytes.toByteArray
  if h_valid : txt.IsValidUTF8 then
    let s := String.fromUTF8 txt h_valid

    have h_size : s.utf8ByteSize = n := by
      simp only [utf8ByteSize]
      simp only [s, fromUTF8, txt, List.size_toByteArray]
      exact h_len

    return ⟨s, h_size⟩
  else
    none

theorem String.serialize_len (s : String) :
  s.serialize.length = s.utf8ByteSize := by
  rw [utf8ByteSize_ofByteArray]
  simp only [String.serialize, toUTF8_eq_bytes]
  exact @Array.size_eq_length_toList UInt8 s.bytes.data

theorem String.parser_len (len : Nat) (s : String) (inp rest : List UInt8) :
  (String.parser len).run inp = some (s, rest) → s.utf8ByteSize = len := by
  simp only [String.parser]
  simp only [StateT.run_bind, Option.bind_eq_bind, Option.bind]
  intro h
  split at h
  · contradiction
  · next bytes h_parse =>
    simp only at h
    split at h
    · next h_valid =>
      simp at h
      have h_len := bytesParser_len _ _ _ _ h_parse
      rw [←h.1]
      simp only [fromUTF8, utf8ByteSize_ofByteArray, List.size_toByteArray]
      exact h_len
    · contradiction

-- theorem String.roundtrip (s : String) (rest : List UInt8) :
--   (String.parser s.serialize.length).run (s.serialize ++ rest) = some (s, rest) := by
--   simp only [String.serialize, String.parser]
--   simp only [toUTF8_eq_bytes, StateT.run_bind, Option.bind_eq_bind, Option.bind]
--   split
--   { next val h_eq =>
--     simp [roundtrip_bytes _ _, reduceCtorEq] at h_eq
--   }
--   { next val h_eq =>
--     rw [roundtrip_bytes _ _] at h_eq
--     simp only
--     injection h_eq with h_eq
--     split
--     { next h_utf8 =>
--       simp [liftM, monadLift, MonadLift.monadLift]
--       subst h_eq
--       simp only [and_true]
--       congr
--       apply bytearray_list_roundtrip
--     }
--     { next h_wrong =>
--       rw [←h_eq] at h_wrong
--       simp only [bytearray_list_roundtrip] at h_wrong
--       exact absurd s.isValidUTF8 h_wrong
--     }
--   }

theorem String.roundtrip (s : String) (rest : List UInt8) :
  (String.parser s.serialize.length).run (s.serialize ++ rest) = some (s, rest) := by
  simp only [String.serialize, String.parser]
  simp only [toUTF8_eq_bytes, StateT.run_bind, Option.bind_eq_bind, Option.bind]
  rw [roundtrip_bytes]
  simp only
  split
  · next h =>
    simp [String.fromUTF8, bytearray_list_roundtrip]
  · next h =>
    simp [bytearray_list_roundtrip] at h
    exact absurd s.isValidUTF8 h

theorem String.roundtrip_proof (s : String) (rest : List UInt8) :
  (String.parserWithProof s.serialize.length).run (s.serialize ++ rest) = some (⟨s, s.serialize_len.symm⟩, rest) := by
  simp only [String.parserWithProof]
  simp only [StateT.run_bind, Option.bind_eq_bind, Option.bind]
  split
  { next x val h_eq =>
    rw [roundtrip_bytes_with_proof _ _] at h_eq
    contradiction
  }
  { next val h_eq =>
    rw [roundtrip_bytes_with_proof _ _] at h_eq
    simp only
    injection h_eq with h_eq
    split
    { next h_utf8 =>
      simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq]
      subst h_eq
      simp only [and_true]
      congr
      apply bytearray_list_roundtrip
    }
    { next h_wrong =>
      rw [←h_eq] at h_wrong
      simp [String.serialize, bytearray_list_roundtrip] at h_wrong
      exact absurd s.isValidUTF8 h_wrong
    }
  }

theorem String.parserWithProof_eq_parser_success (n : Nat) (inp : List UInt8)
  (s : String) (rest : List UInt8) :
  (String.parser n).run inp = some (s, rest) →
  ∃ h, (String.parserWithProof n).run inp = some (⟨s, h⟩, rest) := by
  intro h_simple
  have h_parser_len := String.parser_len _ _ _ _ h_simple

  -- Unfold both parsers
  simp only [String.parser, String.parserWithProof] at *
  simp only [StateT.run_bind, Option.bind_eq_bind, Option.bind] at *

  -- Step through the simple parser to extract facts
  split at h_simple
  · contradiction -- bytesParser failed
  · next bytes h_bytes =>
    simp only at h_simple
    split at h_simple
    · next h_utf8 =>
      -- If simple parser succeeded, bytesParserWithProof must succeed too
      -- We construct the proof needed for the dependent parser
      simp at h_simple
      have ⟨h_len, h_parsed⟩ := bytesParserWithProof_eq_parser_success _ _ _ _ h_bytes
      rw [h_parsed]
      simp [h_utf8]
      repeat' constructor
      · exact h_simple.left
      · exact h_parser_len
      · exact h_simple.right
    · contradiction


/-
/-- Simple Serializer: just a list of bytes for now (easier to prove than ByteArray) -/
abbrev Serializer := List UInt8

/-- The Parser Monad: State is the remaining bytes -/
abbrev Parser (α : Type) := StateT (List UInt8) Option α

/-- 1. Define the Primitive: Read one byte -/
def parseByte : Parser UInt8 := do
  match (← get) with
  | [] => failure
  | b :: rest =>
    set rest
    return b

/-- 2. Define the Serializer for the Primitive -/
def serializeByte (b : UInt8) : Serializer := [b]

/-- 3. The Roundtrip Lemma for the Primitive -/
-- "If we parse a serialized byte followed by arbitrary 'rest',
--  we get the byte back and the state becomes 'rest'."
theorem parse_serialize_byte_id (b : UInt8) (rest : List UInt8) :
  parseByte.run (serializeByte b ++ rest) = some (b, rest) := by
  -- The proof is trivial by definition
  rfl

structure MyPacket where
  a : UInt8
  b : UInt8
  deriving Repr, DecidableEq

def parsePacket : Parser MyPacket := do
  let a ← parseByte
  let b ← parseByte
  return { a, b }

def serializePacket (p : MyPacket) : Serializer :=
  serializeByte p.a ++ serializeByte p.b

/-- The Proof for the Complex Type -/
theorem parse_serialize_packet_id (p : MyPacket) (rest : List UInt8) :
  parsePacket.run (serializePacket p ++ rest) = some (p, rest) := by
  -- Expand definitions
  simp [parsePacket, serializePacket]
  -- Apply the lemma for the first byte (p.a)
  rw [parse_serialize_byte_id]
  simp
  -- Apply the lemma for the second byte (p.b)
  rw [parse_serialize_byte_id]
  simp
  -- Done
  rfl
-/
