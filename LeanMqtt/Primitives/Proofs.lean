import Std.Tactic.BVDecide
import Helpers.Proofs

import LeanMqtt.Core.Parser.Proofs
import LeanMqtt.Primitives.Basic
import Helpers.NatifyUInt8
import Helpers.CrushLits

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

theorem UInt8.parser_len (n : UInt8) :
  n.serialize.length = 1 := by
    rfl

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
  simp only [String.serialize, String.toUTF8_eq_toByteArray]
  rw [Helpers.bytearray_tolist_eq_data_tolist, ByteArray.size]
  exact @Array.size_eq_length_toList UInt8 s.toByteArray.data

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
  simp only [String.toUTF8_eq_toByteArray, StateT.run_bind, Option.bind_eq_bind, Option.bind]
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
    -- simp [Coe.coe, GetByteSize.byteSize] at h
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

theorem VarInt.roundtrip (v : VarInt) (rest : List UInt8) :
    VarInt.parser.run (v.serialize ++ rest) = some (v, rest) := by

  have ⟨v', h_v_limit⟩ := v
  simp [VarInt.parser]
  unfold VarInt.parser.loop
  unfold VarInt.serialize
  simp [Option.bind, UInt8.parser]

  natify_uint8; simp at *
  crush_lits; simp at *

  if h₁ : v' < 128 then
    simp [h₁]

    have : ¬128 ≤ v' % 256 := by omega
    simp [if_neg this]

    have : v' % 128 < limit := by
      rw [Nat.mod_eq_of_lt]
      · exact h_v_limit
      · apply h₁
    simp [dif_pos this]
    exact h₁
  else
    simp [h₁]

    have : 128 ≤ (v' % 128 + 128) % 256 := by omega
    simp [if_pos this]

    unfold VarInt.parser.loop
    unfold VarInt.serialize
    simp [UInt8.parser]
    natify_uint8; simp at *
    crush_lits; simp at *

    if h₂ : v' / 128 < 128 then
      simp [h₂]
      have : ¬v' / 128 % 256 = 0 := by omega
      simp [if_neg this]

      have : ¬128 ≤ v' / 128 % 256 := by omega
      simp [if_neg this]

      have : v' / 128 % 128 * 128 + v' % 128 < 268435456 := by omega
      simp [dif_pos this]
      omega
    else
      simp [h₂]
      have : ¬((v' / 128 % 128 + 128) % 256 = 0) := by omega
      simp [if_neg this]

      have : 128 ≤ (v' / 128 % 128 + 128) % 256 := by omega
      simp [if_pos this]

      unfold VarInt.parser.loop
      unfold VarInt.serialize
      simp [UInt8.parser]
      natify_uint8; simp at *
      crush_lits; simp at *

      if h₃ : v' / 128 / 128 < 128 then
        simp [h₃]

        have : ¬v' / 128 / 128 % 256 = 0 := by omega
        simp [if_neg this]

        have : ¬128 ≤ v' / 128 / 128 % 256 := by omega
        simp [if_neg this]

        have : v' / 128 / 128 % 128 * 16384
          + (v' / 128 % 128 * 128 + v' % 128) < 268435456 := by omega
        simp [dif_pos this]

        omega
      else
        simp [h₃]

        have : ¬(v' / 128 / 128 % 128 + 128) % 256 = 0 := by omega
        simp [if_neg this]

        have : 128 ≤ (v' / 128 / 128 % 128 + 128) % 256 := by omega
        simp [if_pos this]

        unfold VarInt.parser.loop
        unfold VarInt.serialize
        simp [UInt8.parser]
        natify_uint8; simp at *
        crush_lits; simp at *

        if h₄ : v' / 128 / 128 / 128 < 128 then
          simp [h₄]

          have : ¬v' / 128 / 128 / 128 % 256 = 0 := by omega
          simp [if_neg this]

          have : ¬128 ≤ v' / 128 / 128 / 128 % 256 := by omega
          simp [if_neg this]

          have : v' / 128 / 128 / 128 % 128 * 2097152
            + (v' / 128 / 128 % 128 * 16384
            + (v' / 128 % 128 * 128 + v' % 128)) < 268435456 := by omega
          simp [dif_pos this]

          omega
        else
          simp [h₄]
          -- Since `v` is limited by `VarInt.limit`, h₄ must be false.
          grind

example (b : UInt8) : b.toNat < 256 :=
  b.toBitVec.isLt

-- We'll need the theorems below to help `omega` in the `VarInt.parser_reconstruct`
-- proof.
private theorem UInt8.toNat_pos {b : UInt8} (h : ¬b = 0) : 0 < b.toNat := by
  apply Nat.pos_of_ne_zero
  intro h_zero
  apply h
  cases b
  rename_i bv
  have h_bv_eq_zero : bv = 0 := by
    apply BitVec.eq_of_toNat_eq
    exact h_zero
  rw [h_bv_eq_zero]
  rfl

private theorem UInt8.toNat_lt_256 (b : UInt8) : b.toNat < 256 :=
  b.toBitVec.isLt

theorem VarInt.parser_reconstruct
    (input : List UInt8) (v : VarInt) (rest : List UInt8) :
    VarInt.parser.run input = some (v, rest) → input = v.serialize ++ rest := by

  intro h_parse
  have ⟨v', v_h⟩ := v
  have h_cast : (↑(128 : VarInt) : Nat) = 128 := rfl

  simp [VarInt.parser] at h_parse
  unfold VarInt.parser.loop at h_parse
  simp at h_parse
  cases input with
  | nil => contradiction
  | cons b1 rest1 =>
    simp [UInt8.parser] at h_parse
    split at h_parse
    · next h_128_leq_b1 =>
      have h_128_leq_b1_nat : 128 ≤ b1.toNat := h_128_leq_b1
      cases rest1 with
      | nil => contradiction
      | cons b2 rest2 =>
        unfold parser.loop at h_parse
        simp [UInt8.parser] at h_parse
        split at h_parse
        · contradiction
        · next h_b2_neq_0 =>
          have h_b2_neq_0_nat : 0 < b2.toNat := UInt8.toNat_pos h_b2_neq_0
          split at h_parse
          · next h_b2_leq_128 =>
            have h_b2_leq_128_nat : 128 ≤ b2.toNat := h_b2_leq_128
            cases rest2 with
            | nil => contradiction
            | cons b3 rest3 =>
              unfold parser.loop at h_parse
              simp [UInt8.parser] at h_parse
              split at h_parse
              · contradiction
              · next h_b3_neq_0 =>
                have h_b3_neq_0_nat : 0 < b3.toNat := UInt8.toNat_pos h_b3_neq_0
                split at h_parse
                · next h_128_leq_b3 =>
                  have h_128_leq_b3_nat : 128 ≤ b3.toNat := h_128_leq_b3
                  cases rest3 with
                  | nil => contradiction
                  | cons b4 rest4 =>
                    unfold parser.loop at h_parse
                    simp [UInt8.parser] at h_parse
                    split at h_parse
                    · contradiction
                    · next h_b4_neq_0 =>
                      have h_b4_neq_0_nat : 0 < b4.toNat := UInt8.toNat_pos h_b4_neq_0
                      split at h_parse
                      · next h_128_leq_b4 =>
                        unfold parser.loop at h_parse
                        contradiction
                      · next h_128_gt_b4 =>
                        have h_128_gt_b4_nat : ¬128 ≤ b4.toNat := h_128_gt_b4
                        split at h_parse
                        rotate_left
                        · contradiction
                        · next h_limit =>
                          simp at h_parse
                          obtain ⟨h_val, h_rest⟩ := h_parse
                          rw [← h_rest]

                          unfold VarInt.serialize
                          have : ¬v' < 128 := by omega
                          simp [dif_neg this]

                          unfold VarInt.serialize; simp
                          rw [h_cast]
                          have : ¬v' / 128 < 128 := by omega
                          simp [if_neg this]

                          unfold VarInt.serialize
                          simp
                          rw [h_cast]
                          have : ¬v' / 128 / 128 < 128 := by omega
                          simp [if_neg this]

                          unfold VarInt.serialize
                          simp
                          rw [h_cast]
                          have : v' / 128 / 128 / 128 < 128 := by omega
                          simp [if_pos this]

                          refine ⟨?_, ?_, ?_, ?_⟩
                          · apply UInt8.toNat.inj; simp
                            have h_b1_limit := UInt8.toNat_lt_256 b1
                            omega
                          · apply UInt8.toNat.inj; simp
                            have h_b2_limit := UInt8.toNat_lt_256 b2
                            omega
                          · apply UInt8.toNat.inj; simp
                            have h_b2_limit := UInt8.toNat_lt_256 b3
                            omega
                          · apply UInt8.toNat.inj; simp
                            have h_b2_limit := UInt8.toNat_lt_256 b4
                            omega
                · next h_b3_gt_128 =>
                  have h_b3_gt_128 : ¬128 ≤ b3.toNat := h_b3_gt_128
                  split at h_parse
                  · next h_limit =>
                    simp at h_parse
                    obtain ⟨h_val, h_rest⟩ := h_parse
                    rw [← h_rest]

                    unfold VarInt.serialize; simp
                    have : ¬v' < 128 := by omega
                    simp [if_neg this]

                    unfold VarInt.serialize; simp
                    rw [h_cast]
                    have : ¬v' / 128 < 128 := by omega
                    simp [if_neg this]

                    unfold VarInt.serialize; simp
                    rw [h_cast]
                    have : v' / 128 / 128 < 128 := by omega
                    simp [if_pos this]

                    refine ⟨?_, ?_, ?_⟩
                    · apply UInt8.toNat.inj; simp
                      have h_b1_limit := UInt8.toNat_lt_256 b1
                      omega
                    · apply UInt8.toNat.inj; simp
                      have h_b2_limit := UInt8.toNat_lt_256 b2
                      omega
                    · apply UInt8.toNat.inj; simp
                      have h_b3_limit := UInt8.toNat_lt_256 b3
                      omega
                  · contradiction
          · next h_128_le_b2 =>
            have h_128_le_b2_nat : ¬128 ≤ b2.toNat := h_128_le_b2
            split at h_parse
            · next h_limit =>
              simp at h_parse
              obtain ⟨h_val, h_rest⟩ := h_parse
              rw [← h_rest]

              unfold VarInt.serialize; simp
              have : ¬v' < 128 := by omega
              simp [if_neg this]

              unfold VarInt.serialize; simp
              rw [h_cast]
              have : v' / 128 < 128 := by omega
              simp [if_pos this]

              refine ⟨?_, ?_⟩
              · apply UInt8.toNat.inj; simp
                have h_b1_limit := UInt8.toNat_lt_256 b1
                omega
              · apply UInt8.toNat.inj; simp
                have h_b2_limit := UInt8.toNat_lt_256 b2
                omega
            · contradiction
    · next h_128_gt_b1 =>
      have h_128_gt_b1_nat : ¬128 ≤ b1.toNat := h_128_gt_b1
      split at h_parse
      · next h_limit =>
        simp at h_parse
        obtain ⟨h_val, h_rest⟩ := h_parse
        rw [← h_rest]

        unfold VarInt.serialize; simp
        have : v' < 128 := by omega
        simp [if_pos this]

        apply UInt8.toNat.inj; simp
        have h_b1_limit := UInt8.toNat_lt_256 b1
        omega
      · contradiction

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
