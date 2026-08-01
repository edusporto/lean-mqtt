import Std.Tactic.BVDecide
import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Primitives.UInt.Proofs
import LeanMqtt.Primitives.VarInt.Proofs
import LeanMqtt.Helpers.ParserTactics

namespace Mqtt
open Mqtt

theorem PktKind.roundtrip (k : PktKind) :
    PktKind.decode? k.encode = some k := by
  cases k <;> rfl

theorem PktFlags.roundtrip (k : PktKind) (f : PktFlags k) :
    PktFlags.decode? k (PktFlags.encode k f) = some f := by
  cases k
  case publish =>
    rcases f with ⟨⟨dup, ⟨qos_val, h_qos⟩, retain⟩, h_raw⟩
    dsimp only [PktFlags.encode, PktFlags.decode?]

    have h_dup : BitVec.extractLsb 3 3 (dup ++ qos_val ++ retain) = dup := by bv_decide
    have h_q   : BitVec.extractLsb 2 1 (dup ++ qos_val ++ retain) = qos_val := by bv_decide
    have h_ret : BitVec.extractLsb 0 0 (dup ++ qos_val ++ retain) = retain := by bv_decide

    rw [h_dup, h_q, h_ret]
    rw [dif_pos h_qos]
    rw [dif_pos h_raw]

  all_goals {
    rcases f with ⟨val, hval⟩
    simp [encode, decode?, hval]
  }

theorem PktKind.reconstruct {b : BitVec 4} {k : PktKind} :
    PktKind.decode? b = some k → b = k.encode := by
  intro h
  unfold PktKind.decode? at h
  split at h <;> cases h <;> rfl

theorem PktFlags.reconstruct {k : PktKind} {b : BitVec 4} {f : PktFlags k} :
    PktFlags.decode? k b = some f → b = PktFlags.encode k f := by
  intro h

  cases k <;> dsimp only [PktFlags.decode?] at h

  case publish =>
    split at h
    · split at h
      · cases h
        unfold PktFlags.encode
        bv_decide
      · contradiction
    · contradiction

  all_goals {
    split at h
    · cases h
      unfold PktFlags.encode
      rfl
    · contradiction
  }

theorem FixedHeader.roundtrip (header : FixedHeader) {rest : List UInt8} :
    FixedHeader.parser.run (header.serialize ++ rest) = some (header, rest) := by

  simp [FixedHeader.parser, FixedHeader.serialize, UInt8.parser]
  simp [Option.bind]

  let reading := (header.kind.encode ++ PktFlags.encode header.kind header.flags)
  have h_upper : BitVec.extractLsb 7 4 reading = header.kind.encode := by bv_decide
  have h_lower : BitVec.extractLsb 3 0 reading = PktFlags.encode header.kind header.flags := by bv_decide
  rw [h_upper, h_lower]

  simp [PktKind.roundtrip, PktFlags.roundtrip, VarInt.roundtrip]

theorem FixedHeader.reconstruct {header : FixedHeader} {input rest : List UInt8} :
    FixedHeader.parser.run input = some (header, rest) →
    input = header.serialize ++ rest := by

  simp only [FixedHeader.parser, FixedHeader.serialize]
  intro h

  -- Linearly extract every single parsed line from the `do` block
  step_parser h → byteVal rest1 h_byteVal
  step_parser h → kindVal rest2 h_kindVal
  step_parser h → flagsVal rest3 h_flagsVal
  step_parser h → sizeVal rest4 h_sizeVal

  -- Extract the pure return and align our goal
  finish_parser h → h_result
  subst h_result

  -- Unpack the lifted options.
  -- This proves that the state didn't move (rest2 = rest1, rest3 = rest2) and
  -- gives us the raw Option truths.
  finish_parser h_kindVal → h_k_opt
  finish_parser h_flagsVal → h_f_opt

  -- Reconstruction proofs
  rw [UInt8.reconstruct h_byteVal, VarInt.reconstruct h_sizeVal]
  simp only [UInt8.serialize, List.append_assoc]

  -- Substitute the BitVec equality to prove the UInt8 byte matches
  have h_byte_eq : byteVal = UInt8.ofBitVec (kindVal.encode ++ PktFlags.encode kindVal flagsVal) := by
    have h_byte_bv : byteVal.toBitVec = (kindVal.encode ++ PktFlags.encode kindVal flagsVal) := by
      rw [← PktKind.reconstruct h_k_opt, ← PktFlags.reconstruct h_f_opt]
      bv_decide
    rw [←h_byte_bv]

  rw [h_byte_eq]

theorem FixedHeader.serialize_len (h : FixedHeader) :
    h.serialize.length = GetByteSize.byteSize h := by
  simp only [FixedHeader.serialize, GetByteSize.byteSize, FixedHeader.byteSize]
  simp only [List.length_append, List.length_singleton]
  rfl

end Mqtt
