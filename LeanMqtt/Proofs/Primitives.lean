import LeanMqtt.Serialization.Primitives
import Std.Tactic.BVDecide
import Helpers.Proofs

namespace Mqtt
open Mqtt

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


theorem String.serialize_len (s : String) :
  s.serialize.length = s.utf8ByteSize := by
  rw [String.utf8ByteSize_ofByteArray]
  simp only [String.serialize, String.toUTF8_eq_bytes]
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
      simp only [String.fromUTF8, String.utf8ByteSize_ofByteArray, List.size_toByteArray]
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
  simp only [String.toUTF8_eq_bytes, StateT.run_bind, Option.bind_eq_bind, Option.bind]
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

theorem Str.roundtrip (s : Str) (rest : List UInt8) :
  Str.parser.run (s.serialize ++ rest) = some (s, rest) := by
  simp only [Str.parser, Str.serialize]
  simp only [
    bind_pure_comp, List.append_assoc, StateT.run_bind, StateT.run_map,
    Option.map_eq_map, Option.bind_eq_bind
  ]

  rw [UInt16.roundtrip _ _]
  simp only [Option.bind_some, Option.map]

  have h_len_eq : s.len.val.toNat = s.val.serialize.length := by
    rw [String.serialize_len]
    have h := s.len.property
    -- simp [Coe.coe, GetLength.length] at h
    exact h

  /-
    To use the String.roundtrip theorem, we need to substitute `s.len.val.toNat`
    with `s.val.serialize.length`. However, due to dependent type shenanigans,
    we can't do this substitution in `String.parserWithProof`. So, we do the
    substitution in the simple parser (`String.parser`), then use the projection
    lemma (`String.parserWithProof_eq_parser_success`) to show it also holds for
    `String.parserWithProof`.
  -/
  have h_simple := String.roundtrip s.val rest

  rw [←h_len_eq] at h_simple
  have ⟨_, h_dep⟩ := String.parserWithProof_eq_parser_success _ _ _ _ h_simple

  rw [h_dep]

theorem StrPair.roundtrip (p : StrPair) (rest : List UInt8) :
  StrPair.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp only [StrPair.parser, StrPair.serialize]
  simp only [
    bind_pure_comp, List.append_assoc, StateT.run_bind, StateT.run_map,
    Option.map_eq_map, Option.map, Option.bind_eq_bind, Option.bind
  ]
  simp only [Str.roundtrip _ _]

theorem BinaryData.roundtrip (b : BinaryData) (rest : List UInt8) :
  BinaryData.parser.run (b.serialize ++ rest) = some (b, rest) := by
  simp only [BinaryData.parser, BinaryData.serialize]
  simp [Option.bind, Option.map]

  rw [UInt16.roundtrip _ _]
  simp only

  have h_len_eq : b.len.val.toNat = b.val.toList.length := by
    simp only [Array.length_toList]
    have h := b.len.property
    exact h

  /-
    Due to dependent type shenanigans, we can't rewrite the current goal
    with `h_len_eq`. So, we rewrite it in the simpler parser, and prove
    that it implies our current goal. See `Str.roundtrip` for more.
  -/
  have h_simple := roundtrip_bytes b.val.toList rest
  rw [←h_len_eq] at h_simple
  have ⟨_, h_dep⟩ := bytesParserWithProof_eq_parser_success _ _ _ _ h_simple

  rw [h_dep]

-- TODO: this proof is beyond my pay grade
theorem VarInt.roundtrip (v : VarInt) (rest : List UInt8) :
  VarInt.parser.run (v.serialize ++ rest) = some (v, rest) :=
  sorry

/--
  Executable checker: Returns true if 'n' survives the roundtrip.
  Note: We use strict equality checks.
-/
def checksOut (n : VarInt) : Bool :=
  let bytes := VarInt.serialize n
  match VarInt.parser.run bytes with
  | some (v, []) => v.val == n
  | _ => false

/-- Checks 'checksOut' for all numbers from 'start' up to 'limit' -/
def checkRange (start limit : Nat) : Bool :=
  if start >= limit then
    true
  else if h : ¬(start < VarInt.limit) then
    false
  else if checksOut ⟨start, Decidable.of_not_not h⟩ then
    checkRange (start + 1) limit
  else
    false

end Mqtt
