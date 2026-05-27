import Std.Tactic.BVDecide
import LeanMqtt.Helpers.Proofs
import LeanMqtt.Helpers.NatifyUInt8
import LeanMqtt.Helpers.CrushLits

import LeanMqtt.Core.Parser.Proofs
import LeanMqtt.Core.Codec
import LeanMqtt.Primitives.Basic

namespace Mqtt
open Mqtt

theorem UInt8.parser_len (n : UInt8) :
    n.serialize.length = 1 := by
  rfl

theorem UInt8.roundtrip (b : UInt8) {rest : List UInt8} :
    UInt8.parser.run (b.serialize ++ rest) = some (b, rest) := by
    simp [UInt8.parser, UInt8.serialize]

theorem UInt8.reconstruct {b : UInt8} {input rest : List UInt8} :
    UInt8.parser.run input = some (b, rest) → input = b.serialize ++ rest := by
  simp [UInt8.parser, UInt8.serialize, StateT.run_bind, StateT.run_get]
  split
  · intro h
    contradiction
  · intro h
    simp at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    rfl

theorem UInt16.parser_len (n : UInt16) :
    n.serialize.length = 2 := by
  rfl

theorem UInt16.roundtrip (n : UInt16) {rest : List UInt8} :
    UInt16.parser.run (n.serialize ++ rest) = some (n, rest) := by
  simp [UInt16.parser, UInt16.serialize, UInt8.parser]
  bv_decide

theorem UInt16.reconstruct {n : UInt16} {input rest : List UInt8} :
    UInt16.parser.run input = some (n, rest) → input = n.serialize ++ rest := by

  simp only [UInt16.parser, UInt16.serialize]
  intro h

  obtain ⟨b1, mid, h_b1, h_next1⟩ := Parser.bind_run_success h
  obtain ⟨b2, mid2, h_b2, h_next2⟩ := Parser.bind_run_success h_next1
  obtain ⟨h_n, h_rest⟩ := Parser.pure_run_success h_next2

  subst h_rest h_n

  have h_rec1 := UInt8.reconstruct h_b1
  have h_rec2 := UInt8.reconstruct h_b2

  rw [h_rec1, h_rec2]
  simp [UInt8.serialize, List.cons_append, List.nil_append]
  bv_decide

theorem UInt32.parser_len (n : UInt32) :
    n.serialize.length = 4 := by
  rfl

theorem UInt32.roundtrip (n : UInt32) {rest : List UInt8} :
    UInt32.parser.run (n.serialize ++ rest) = some (n, rest) := by
  simp [UInt32.parser, UInt32.serialize, UInt8.parser, Option.bind, Option.map]
  bv_decide

theorem UInt32.reconstruct {n : UInt32} {input rest : List UInt8} :
    UInt32.parser.run input = some (n, rest) → input = n.serialize ++ rest := by

  simp only [UInt32.parser, UInt32.serialize]
  intro h

  obtain ⟨b1, mid1, h_b1, h_next1⟩ := Parser.bind_run_success h
  obtain ⟨b2, mid2, h_b2, h_next2⟩ := Parser.bind_run_success h_next1
  obtain ⟨b3, mid3, h_b3, h_next3⟩ := Parser.bind_run_success h_next2
  obtain ⟨b4, mid4, h_b4, h_next4⟩ := Parser.bind_run_success h_next3
  obtain ⟨h_n, h_rest⟩ := Parser.pure_run_success h_next4

  subst h_rest h_n

  have h_rec1 := UInt8.reconstruct h_b1
  have h_rec2 := UInt8.reconstruct h_b2
  have h_rec3 := UInt8.reconstruct h_b3
  have h_rec4 := UInt8.reconstruct h_b4

  rw [h_rec1, h_rec2, h_rec3, h_rec4]
  simp [UInt8.serialize, List.cons_append, List.nil_append]
  bv_decide

theorem String.serialize_len (s : String) :
    s.serialize.length = s.utf8ByteSize := by
  rw [String.utf8ByteSize_ofByteArray]
  simp [String.serialize, String.toUTF8_eq_toByteArray]
  rw [Helpers.bytearray_tolist_eq_data_tolist]
  unfold String.utf8ByteSize
  exact @Array.size_eq_length_toList UInt8 s.toByteArray.data

theorem String.parser_len {len : Nat} {s : String} {inp rest : List UInt8} :
    (String.parser len).run inp = some (s, rest) → s.utf8ByteSize = len := by
  simp [String.parser]
  simp [Option.bind]
  intro h
  split at h
  · contradiction
  · next bytes h_parse =>
    simp only at h
    split at h
    · next h_valid =>
      simp at h
      have h_len := Parser.bytes_len h_parse
      rw [←h.1]
      simp only [String.fromUTF8, String.utf8ByteSize_ofByteArray, List.size_toByteArray]
      exact h_len
    · contradiction

theorem String.roundtrip (s : String) {rest : List UInt8} :
    (String.parser s.serialize.length).run (s.serialize ++ rest) = some (s, rest) := by
  simp only [String.serialize, String.parser]
  simp [String.toUTF8_eq_toByteArray, Option.bind]
  rw [Parser.bytes_roundtrip]
  simp
  split
  · next h =>
    simp [String.fromUTF8, Helpers.bytearray_list_roundtrip]
  · next h =>
    simp [Helpers.bytearray_list_roundtrip] at h
    exact absurd s.isValidUTF8 h

theorem String.roundtrip_proof (s : String) {rest : List UInt8} :
    (String.parserWithProof s.serialize.length).run (s.serialize ++ rest) =
    some (⟨s, s.serialize_len.symm⟩, rest) := by
  simp [String.parserWithProof]
  simp [Option.bind]
  split
  · next x val h_eq =>
    rw [Parser.bytesWithProof_roundtrip _ _] at h_eq
    contradiction
  · next val h_eq =>
    rw [Parser.bytesWithProof_roundtrip _ _] at h_eq
    simp only
    injection h_eq with h_eq
    split
    · next h_utf8 =>
      simp
      subst h_eq
      simp only [and_true]
      congr
      apply Helpers.bytearray_list_roundtrip
    · next h_wrong =>
      rw [←h_eq] at h_wrong
      simp [String.serialize, Helpers.bytearray_list_roundtrip] at h_wrong
      exact absurd s.isValidUTF8 h_wrong

theorem String.reconstructWithProof {len : Nat} {s : { s : String // s.utf8ByteSize = len }}
    {input rest : List UInt8} :
    (String.parserWithProof len).run input = some (s, rest) → input = s.val.serialize ++ rest := by

  simp only [String.parserWithProof, String.serialize]
  intro h
  obtain ⟨bytes_val, mid, h_bytes, h_next⟩ := Parser.bind_run_success h

  split at h_next
  · next h_valid =>
    obtain ⟨h_s, h_rest⟩ := Parser.pure_run_success h_next
    subst h_rest

    have h_rec := Parser.bytesWithProof_reconstruct h_bytes
    rw [h_rec, h_s]

    simp [String.fromUTF8, String.toUTF8_eq_toByteArray, Helpers.list_bytearray_roundtrip]
  · contradiction

theorem String.parserWithProof_eq_parser_success {n : Nat} {s : String}
    {inp rest : List UInt8} :
    (String.parser n).run inp = some (s, rest) →
    ∃ h, (String.parserWithProof n).run inp = some (⟨s, h⟩, rest) := by
  intro h_simple
  have h_parser_len := String.parser_len h_simple

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
      have ⟨h_len, h_parsed⟩ := Parser.bytes_imp_bytesWithProof h_bytes
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

  rw [UInt16.roundtrip s.len.val]
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
  have h_simple := @String.roundtrip s.val rest

  rw [←h_len_eq] at h_simple
  have ⟨_, h_dep⟩ := String.parserWithProof_eq_parser_success h_simple

  rw [h_dep]

theorem Str.reconstruct {s : Str} {input rest : List UInt8} :
    Str.parser.run input = some (s, rest) → input = s.serialize ++ rest := by

  simp only [Str.parser, Str.serialize]
  intro h

  obtain ⟨len, mid, h_len, h_next⟩ := Parser.bind_run_success h
  obtain ⟨str_val, mid2, h_str, h_next2⟩ := Parser.bind_run_success h_next
  obtain ⟨h_s, h_rest⟩ := Parser.pure_run_success h_next2

  subst h_rest
  have h_rec_len := UInt16.reconstruct h_len
  have h_rec_str := String.reconstructWithProof h_str

  rw [h_rec_len, h_rec_str, h_s]
  simp [List.append_assoc]

theorem StrPair.roundtrip (p : StrPair) {rest : List UInt8} :
    StrPair.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp [StrPair.parser, StrPair.serialize, Option.bind, Option.map]
  simp only [Str.roundtrip _ _]

theorem StrPair.reconstruct {p : StrPair} {input rest : List UInt8} :
    StrPair.parser.run input = some (p, rest) → input = p.serialize ++ rest := by
  simp only [StrPair.parser, StrPair.serialize]
  intro h

  obtain ⟨s1, mid1, h_s1, h_next1⟩ := Parser.bind_run_success h
  obtain ⟨s2, mid2, h_s2, h_next2⟩ := Parser.bind_run_success h_next1

  obtain ⟨h_p, h_rest⟩ := Parser.pure_run_success h_next2
  subst h_p h_rest

  have rec1 := Str.reconstruct h_s1
  have rec2 := Str.reconstruct h_s2

  rw [rec1, rec2, List.append_assoc]

theorem BinaryData.roundtrip (b : BinaryData) {rest : List UInt8} :
    BinaryData.parser.run (b.serialize ++ rest) = some (b, rest) := by
  simp only [BinaryData.parser, BinaryData.serialize]
  simp [Option.bind, Option.map]

  rw [UInt16.roundtrip]
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
  have h_simple := Parser.bytes_roundtrip b.val.toList rest
  rw [←h_len_eq] at h_simple
  have ⟨_, h_dep⟩ := Parser.bytes_imp_bytesWithProof h_simple

  rw [h_dep]

theorem BinaryData.reconstruct {b : BinaryData} {input rest : List UInt8} :
    BinaryData.parser.run input = some (b, rest) → input = b.serialize ++ rest := by

  simp only [BinaryData.parser, BinaryData.serialize]
  intro h

  obtain ⟨len, mid, h_len, h_next⟩ := Parser.bind_run_success h
  obtain ⟨bytes_val, mid2, h_bytes, h_next2⟩ := Parser.bind_run_success h_next
  obtain ⟨h_b, h_rest⟩ := Parser.pure_run_success h_next2

  subst h_rest
  have h_rec_len := UInt16.reconstruct h_len
  have h_rec_bytes := Parser.bytesWithProof_reconstruct h_bytes

  rw [h_rec_len, h_rec_bytes, h_b]
  simp [List.append_assoc]

theorem VarInt.roundtrip (v : VarInt) {rest : List UInt8} :
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

theorem VarInt.reconstruct {v : VarInt} {input rest : List UInt8} :
    VarInt.parser.run input = some (v, rest) → input = v.serialize ++ rest := by

  intro h_parse
  obtain ⟨v', v_h⟩ := v

  -- Initialize parser evaluation
  simp only [VarInt.parser] at h_parse
  unfold VarInt.parser.loop at h_parse
  simp at h_parse

  cases input with
  | nil => contradiction
  | cons b1 rest1 =>
    simp [UInt8.parser] at h_parse
    split at h_parse
    rotate_left -- Handle 1-byte terminal case first
    · next h_b1_stops =>
      split at h_parse
      · next h_limit =>
        -- ==========================================
        -- 1-Byte Success Path
        -- ==========================================
        simp at h_parse
        obtain ⟨h_val, h_rest⟩ := h_parse
        rw [← h_rest]

        unfold VarInt.serialize

        have h1 : v' < 128 := by omega
        simp [if_pos h1]

        natify_uint8; simp at *
        omega
      · contradiction

    · next h_b1_continues =>
      cases rest1 with
      | nil => contradiction
      | cons b2 rest2 =>
        unfold parser.loop at h_parse
        simp [UInt8.parser] at h_parse
        split at h_parse
        · contradiction
        · next h_b2_valid =>
          split at h_parse
          rotate_left -- Handle 2-byte terminal case first
          · next h_b2_stops =>
            split at h_parse
            · next h_limit =>
              -- ==========================================
              -- 2-Byte Success Path
              -- ==========================================
              simp at h_parse
              obtain ⟨h_val, h_rest⟩ := h_parse
              rw [← h_rest]

              unfold VarInt.serialize
              unfold VarInt.serialize
              natify_uint8; simp at *; crush_lits; simp at *

              have h1 : ¬v' < 128 := by omega
              have h2 : v' / 128 < 128 := by omega
              simp [if_neg h1, if_pos h2]

              natify_uint8; simp at *
              exact ⟨by omega, by omega⟩
            · contradiction

          · next h_b2_continues =>
            cases rest2 with
            | nil => contradiction
            | cons b3 rest3 =>
              unfold parser.loop at h_parse
              simp [UInt8.parser] at h_parse
              split at h_parse
              · contradiction
              · next h_b3_valid =>
                split at h_parse
                rotate_left -- Handle 3-byte terminal case first
                · next h_b3_stops =>
                  split at h_parse
                  · next h_limit =>
                    -- ==========================================
                    -- 3-Byte Success Path
                    -- ==========================================
                    simp at h_parse
                    obtain ⟨h_val, h_rest⟩ := h_parse
                    rw [← h_rest]

                    unfold VarInt.serialize
                    unfold VarInt.serialize
                    unfold VarInt.serialize
                    natify_uint8; simp at *; crush_lits; simp at *

                    have h1 : ¬v' < 128 := by omega
                    have h2 : ¬v' / 128 < 128 := by omega
                    have h3 : v' / 128 / 128 < 128 := by omega
                    simp [if_neg h1, if_neg h2, if_pos h3]

                    natify_uint8; simp at *
                    exact ⟨by omega, by omega, by omega⟩
                  · contradiction

                · next h_b3_continues =>
                  cases rest3 with
                  | nil => contradiction
                  | cons b4 rest4 =>
                    unfold parser.loop at h_parse
                    simp [UInt8.parser] at h_parse
                    split at h_parse
                    · contradiction
                    · next h_b4_valid =>
                      split at h_parse
                      rotate_left -- Handle 4-byte terminal case first
                      · next h_b4_stops =>
                        split at h_parse
                        · next h_limit =>
                          -- ==========================================
                          -- 4-Byte Success Path
                          -- ==========================================
                          simp at h_parse
                          obtain ⟨h_val, h_rest⟩ := h_parse
                          rw [← h_rest]

                          unfold VarInt.serialize
                          unfold VarInt.serialize
                          unfold VarInt.serialize
                          unfold VarInt.serialize
                          natify_uint8; simp at *; crush_lits; simp at *

                          have h1 : ¬v' < 128 := by omega
                          have h2 : ¬v' / 128 < 128 := by omega
                          have h3 : ¬v' / 128 / 128 < 128 := by omega
                          have h4 : v' / 128 / 128 / 128 < 128 := by omega
                          simp [if_neg h1, if_neg h2, if_neg h3, if_pos h4]

                          natify_uint8; simp at *
                          exact ⟨by omega, by omega, by omega, by omega⟩
                        · contradiction

                      · next h_b4_continues =>
                        -- Exceeded 4-byte fuel
                        unfold parser.loop at h_parse
                        contradiction

instance : Codec VarInt where
  parser      := VarInt.parser
  serialize   := VarInt.serialize
  roundtrip   := VarInt.roundtrip
  reconstruct := VarInt.reconstruct
