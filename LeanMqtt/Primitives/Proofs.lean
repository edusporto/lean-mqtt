import Std.Tactic.BVDecide
import Helpers.Proofs

import LeanMqtt.Core.Parser.Proofs
import LeanMqtt.Primitives.Basic

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
  rw [Helpers.bytearray_tolist_eq_data_tolist, ByteArray.size]
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

theorem String.roundtrip (s : String) (rest : List UInt8) :
  (String.parser s.serialize.length).run (s.serialize ++ rest) = some (s, rest) := by
  simp only [String.serialize, String.parser]
  simp only [String.toUTF8_eq_bytes, StateT.run_bind, Option.bind_eq_bind, Option.bind]
  rw [roundtrip_bytes]
  simp only
  split
  · next h =>
    simp [String.fromUTF8, Helpers.bytearray_list_roundtrip]
  · next h =>
    simp [Helpers.bytearray_list_roundtrip] at h
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
      apply Helpers.bytearray_list_roundtrip
    }
    { next h_wrong =>
      rw [←h_eq] at h_wrong
      simp [String.serialize, Helpers.bytearray_list_roundtrip] at h_wrong
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

theorem varint_algebra (v mult acc : Nat) :
    (v % 128) * mult + acc + (v / 128) * (mult * 128) = acc + v * mult := by
  calc
    _ = acc + mult * (v % 128) + mult * 128 * (v / 128)     := by ac_rfl
    _ = acc + (mult * (v % 128) + mult * 128 * (v / 128))   := by ac_rfl
    _ = acc + (mult * (v % 128) + mult * (128 * (v / 128))) := by ac_rfl
    _ = acc + mult * (v % 128 + 128 * (v / 128))            := by rw [←Nat.mul_add]
    _ = acc + mult * v                                      := by rw [Nat.mod_add_div]
    _ = acc + v * mult                                      := by ac_rfl

-- TODO: this proof is beyond my pay grade
-- theorem VarInt.roundtrip (v : VarInt) (rest : List UInt8) :
--   VarInt.parser.run (v.serialize ++ rest) = some (v, rest) :=
--   sorry

theorem VarInt.roundtrip (v : VarInt) (rest : List UInt8) :
    VarInt.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [VarInt.parser]
  unfold VarInt.parser.loop
  unfold VarInt.serialize
  simp [Option.bind]

  if h₁ : v.val < 128 then
    simp [h₁, UInt8.parser]

    have : UInt8.ofNat v.val < 128 := by
      rw [UInt8.lt_iff_toNat_lt]
      simp only [UInt8.toNat_ofNat', Nat.reducePow, UInt8.reduceToNat]
      rw [Nat.mod_eq_of_lt]
      · exact h₁
      · apply Nat.lt_trans h₁; decide
    simp [if_pos this]

    have : v.val % 128 < limit := by
      rw [Nat.mod_eq_of_lt]
      · simp
      · apply h₁
    simp [dif_pos this]

    apply Fin.eq_of_val_eq -- same as doing `ext`
    simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
    exact h₁
  else
    simp [h₁, UInt8.parser]

    have : ¬ UInt8.ofNat v.val % 128 + 128 < 128 := by
      rw [UInt8.lt_iff_toNat_lt]
      simp [UInt8.toNat_ofNat', Nat.reducePow, UInt8.reduceToNat]
      rw [Nat.mod_eq_of_lt]
      · simp
      · have h_mod : ↑v % 128 < 128 := Nat.mod_lt ↑v (by decide)
        exact Nat.add_lt_add_right h_mod 128
    simp [if_neg this]

    unfold VarInt.parser.loop
    unfold VarInt.serialize
    simp [Option.bind]

    if h₂ : v.val / (128 : VarInt).val < 128 then
      simp [h₂, UInt8.parser]

      have : UInt8.ofNat (v.val / (128 : VarInt).val) < 128 := by
        rw [UInt8.lt_iff_toNat_lt]
        simp only [UInt8.toNat_ofNat', Nat.reducePow, UInt8.reduceToNat]
        rw [Nat.mod_eq_of_lt]
        · exact h₂
        · apply Nat.lt_trans h₂; decide
      simp [if_pos this]

      have : v.val / (128 : VarInt).val % 128 * 128 + v.val % 128 < limit := by
        grind
      simp [dif_pos this]

      apply Fin.eq_of_val_eq
      simp
      grind
    else
      simp [h₂, UInt8.parser]

      have : ¬ UInt8.ofNat (v.val / (128 : VarInt).val) % 128 + 128 < 128 := by
        simp [UInt8.lt_iff_toNat_lt]
        grind
      simp [if_neg this]

      unfold VarInt.parser.loop
      unfold VarInt.serialize
      simp [Option.bind]

      if h₃ : v.val / (128 : VarInt).val / (128 : VarInt).val < 128 then
        simp [h₃, UInt8.parser]

        have : UInt8.ofNat (v.val / (128 : VarInt).val / (128 : VarInt).val) < 128 := by
          simp [UInt8.lt_iff_toNat_lt]
          grind
        simp [if_pos this]

        have :
          v.val / (128 : VarInt).val / (128 : VarInt).val % 128 * 16384 +
          (v.val / (128 : VarInt).val % 128 * 128 + v.val % 128) < limit
        := by grind
        simp [dif_pos this]

        apply Fin.eq_of_val_eq
        simp
        grind
      else
        simp [h₃, UInt8.parser]

        have : ¬ UInt8.ofNat (v.val / (128 : VarInt).val / (128 : VarInt).val) % 128 + 128 < 128 := by
          simp [UInt8.lt_iff_toNat_lt]
          grind
        simp [if_neg this]

        unfold VarInt.parser.loop
        unfold VarInt.serialize
        simp [Option.bind]

        if h₄ : v.val / (128 : VarInt).val / (128 : VarInt).val / (128 : VarInt).val < 128 then
          simp [h₄, UInt8.parser]

          have :
            UInt8.ofNat (v.val / (128 : VarInt).val / (128 : VarInt).val / (128 : VarInt).val)
              < 128 := by
            simp [UInt8.lt_iff_toNat_lt]
            grind
          simp [if_pos this]

          have :
            v.val / (128 : VarInt).val / (128 : VarInt).val / (128 : VarInt).val % 128 * 2097152 +
              (v.val / (128 : VarInt).val / (128 : VarInt).val % 128 * 16384 +
              (v.val / (128 : VarInt).val % 128 * 128 + v.val % 128)) < limit := by
            grind
          simp [dif_pos this]

          ext
          simp
          grind
        else
          simp [h₄, UInt8.parser]

          have :
            ¬ UInt8.ofNat (v.val / (128 : VarInt).val / (128 : VarInt).val / (128 : VarInt).val)
            % 128 + 128 < 128 := by
            simp [UInt8.lt_iff_toNat_lt]
            grind
          simp [if_neg this]

          unfold VarInt.parser.loop
          unfold VarInt.serialize
          simp

          -- Since `v` is limited by `VarInt.limit`, h₄ must be false.
          -- Grind solves the contradiction for us
          grind

-- theorem VarInt.roundtrip (v : VarInt) (rest : List UInt8) :
--     VarInt.parser.run (v.serialize ++ rest) = some (v, rest) := by
--   -- 1. Unfold the parser definition to expose the loop
--   simp only [parser]

--   -- 2. Define the inputs for the general lemma
--   let inputs := v.val
--   let mult := 1
--   let acc := 0
--   let fuel := 4

--   -- 3. Formulate the Generalized Lemma
--   -- We prove this by induction on 'inputs' (v.val) using the same well-founded
--   -- relation as the 'serialize' function.
--   have loop_spec (x : Nat) (m a f : Nat) :
--       f ≥ (VarInt.mk x (sorry)).serialize.length → -- Enough fuel
--       a + x * m < VarInt.limit →                   -- Result fits in limit
--       VarInt.parser.loop m a f ((VarInt.mk x (sorry)).serialize ++ rest) =
--       some (⟨a + x * m, sorry⟩, rest) := by

--     induction x using VarInt.serialize.induct generalizing m a f rest with
--     | case1 x h_small =>
--       -- BASE CASE: x < 128 (1 byte)
--       intro h_fuel h_limit
--       -- Unfold loop (it consumes 1 fuel)
--       unfold VarInt.parser.loop

--       -- We need to show fuel is at least 1
--       match f with
--       | 0 =>
--         -- Contradiction: serialize length is at least 1
--         simp [VarInt.serialize, h_small] at h_fuel
--         contradiction
--       | f' + 1 =>
--         -- Calculate the parser step
--         simp only [VarInt.serialize, h_small, UInt8.parser, StateT.run, bind, Option.bind]

--         -- Logic: b < 128 is true because x < 128
--         have h_cond : (x.toUInt8 : Nat) < 128 := by
--           simp [x.toUInt8_toNat, h_small]

--         simp [h_cond]

--         -- Prove the value equals the expected result
--         -- Goal: (x % 128) * m + a = a + x * m
--         rw [Nat.mod_eq_of_lt h_small]
--         rw [Nat.add_comm, Nat.mul_comm]

--         -- Prove the limit check passes
--         simp [h_limit]

--     | case2 x h_large ih =>
--       -- RECURSIVE CASE: x >= 128
--       intro h_fuel h_limit

--       -- Unfold serialize for the head byte
--       rw [VarInt.serialize]
--       simp [h_large] -- Enter 'else' branch

--       -- Unfold loop (consumes 1 fuel)
--       unfold VarInt.parser.loop

--       match f with
--       | 0 =>
--          -- Contradiction: serialize length > 1
--          simp [VarInt.serialize, h_large] at h_fuel
--          contradiction
--       | f' + 1 =>
--         simp only [UInt8.parser, StateT.run, bind, Option.bind]

--         -- Logic: The byte is ((x % 128) + 128). This is >= 128.
--         -- So the parser will take the 'else' branch (continue looping).
--         have h_byte_val : ((x % 128 + 128).toUInt8.toNat) = x % 128 + 128 := by
--           -- Proof that toUInt8 doesn't overflow (since mod 128 + 128 < 256)
--           sorry -- (Standard Nat/UInt8 arithmetic)

--         rw [h_byte_val]

--         -- Check loop condition: b < 128 is false
--         have h_not_small : ¬ (x % 128 + 128 < 128) := by simp_arith
--         simp [h_not_small]

--         -- APPLY INDUCTION HYPOTHESIS
--         -- We recurse with:
--         --   New x:    x / 128
--         --   New mult: m * 128
--         --   New acc:  (x % 128) * m + a
--         apply ih
--         · -- Proof: Fuel is sufficient (fuel - 1 >= length - 1)
--           simp [VarInt.serialize, h_large] at h_fuel
--           exact Nat.le_of_succ_le_succ h_fuel
--         · -- Proof: The accumulated result is the same!
--           -- (a + (x % 128)*m) + (x / 128) * (m * 128) = a + x * m
--           rw [varint_algebra]
--           exact h_limit

--   -- 4. Apply the lemma to the initial state
--   -- x = v.val, mult = 1, acc = 0, fuel = 4
--   exact loop_spec v.val 1 0 4 (sorry) (sorry)

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
