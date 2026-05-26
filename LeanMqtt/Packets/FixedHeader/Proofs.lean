import Std.Tactic.BVDecide
import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Primitives.Proofs

namespace Mqtt
open Mqtt

theorem PktKind.decode_encode (k : PktKind) :
    PktKind.decode? k.encode = some k := by
  cases k <;> rfl

theorem PktFlags.encode_decode (k : PktKind) (f : PktFlags k) :
    PktFlags.decode? k (PktFlags.encode k f) = some f := by
  cases k
  case publish =>
    rcases f with ⟨dup, ⟨qos_val, h_qos⟩, retain⟩
    simp [encode, decode?]

    have h_dup : BitVec.extractLsb 3 3 (dup ++ qos_val ++ retain) = dup := by bv_decide
    have h_q   : BitVec.extractLsb 2 1 (dup ++ qos_val ++ retain) = qos_val := by bv_decide
    have h_ret : BitVec.extractLsb 0 0 (dup ++ qos_val ++ retain) = retain := by bv_decide

    simp [h_dup, h_q, h_ret]
    assumption

  all_goals {
    rcases f with ⟨val, hval⟩
    simp [encode, decode?, hval]
  }

theorem PktKind.decode_eq_encode (b : BitVec 4) (k : PktKind) :
    PktKind.decode? b = some k → b = k.encode := by
  intro h
  unfold PktKind.decode? at h
  split at h <;> cases h <;> rfl

theorem PktFlags.decode_eq_encode (k : PktKind) (b : BitVec 4) (f : PktFlags k) :
    PktFlags.decode? k b = some f → b = PktFlags.encode k f := by
  intro h

  cases k <;> dsimp only [PktFlags.decode?] at h

  case publish =>
    split at h
    · contradiction
    · cases h
      unfold PktFlags.encode
      bv_decide

  all_goals {
    split at h
    · cases h
      unfold PktFlags.encode
      rfl
    · contradiction
  }

theorem FixedHeader.roundtrip (header : FixedHeader) (rest : List UInt8) :
    FixedHeader.parser.run (header.serialize ++ rest) = some (header, rest) := by

  simp [FixedHeader.parser, FixedHeader.serialize, UInt8.parser]
  simp [Option.bind]

  let reading := (header.kind.encode ++ PktFlags.encode header.kind header.flags)
  have h_upper : BitVec.extractLsb 7 4 reading = header.kind.encode := by bv_decide
  have h_lower : BitVec.extractLsb 3 0 reading = PktFlags.encode header.kind header.flags := by bv_decide
  rw [h_upper, h_lower]

  rw [PktKind.decode_encode]
  simp

  rw [PktFlags.encode_decode]
  simp

  rw [VarInt.roundtrip]
  simp

theorem FixedHeader.reconstruct (input : List UInt8) (header : FixedHeader) (rest : List UInt8) :
    FixedHeader.parser.run input = some (header, rest) → input = header.serialize ++ rest := by

  simp only [FixedHeader.parser, FixedHeader.serialize]
  intro h

  -- Linearly extract every single parsed line from the `do` block
  obtain ⟨byte, mid1, h_byte, h_next1⟩   := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨kind, mid2, h_kind, h_next2⟩   := Parser.bind_run_success _ _ _ _ _ h_next1
  obtain ⟨flags, mid3, h_flags, h_next3⟩ := Parser.bind_run_success _ _ _ _ _ h_next2
  obtain ⟨size, mid4, h_size, h_pure⟩    := Parser.bind_run_success _ _ _ _ _ h_next3

  -- Extract the pure return and align our goal
  obtain ⟨h_header, h_rest⟩ := Parser.pure_run_success _ _ _ _ h_pure
  subst h_rest

  -- Use forward rewrite, or `subst` to replace `header` everywhere
  subst h_header

  -- Unpack the lifted options.
  -- This proves that the state didn't move (mid1 = mid2 = mid3) and
  -- gives us the raw Option truths.
  obtain ⟨h_k_opt, h_mid2⟩ := Parser.liftM_run_success _ _ _ _ h_kind
  obtain ⟨h_f_opt, h_mid3⟩ := Parser.liftM_run_success _ _ _ _ h_flags
  subst h_mid2 h_mid3

  -- Gather reconstruction truths
  have h_rec_byte := UInt8.reconstruct _ _ _ h_byte
  have h_rec_size := VarInt.reconstruct _ _ _ h_size
  have h_k_eq := PktKind.decode_eq_encode _ _ h_k_opt
  have h_f_eq := PktFlags.decode_eq_encode _ _ _ h_f_opt

  rw [h_rec_byte, h_rec_size]
  simp only [UInt8.serialize, List.append_assoc]

  -- Prove the 8-bit vector equals the concatenated 4-bit vectors
  have h_byte_bv : byte.toBitVec = (kind.encode ++ PktFlags.encode kind flags) := by
    rw [←h_k_eq, ←h_f_eq]
    bv_decide

  -- Substitute the BitVec equality to prove the UInt8 byte matches
  have h_byte_eq : byte = UInt8.ofBitVec (kind.encode ++ PktFlags.encode kind flags) := by
    rw [←h_byte_bv]

  rw [h_byte_eq]

end Mqtt
