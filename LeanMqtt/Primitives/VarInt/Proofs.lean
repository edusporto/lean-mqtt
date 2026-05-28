import LeanMqtt.Helpers.NatifyUInt8
import LeanMqtt.Helpers.CrushLits
import LeanMqtt.Core.Codec
import LeanMqtt.Primitives.VarInt.Basic
import LeanMqtt.Primitives.UInt.Proofs

namespace Mqtt
open Mqtt

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
              omega
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
                    omega
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
                          omega
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

end Mqtt
