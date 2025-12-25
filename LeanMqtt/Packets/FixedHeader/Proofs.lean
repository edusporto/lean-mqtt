import Std.Tactic.BVDecide
import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Primitives.Proofs

namespace Mqtt
open Mqtt

theorem WhichPkt.encode_decode (which : WhichPkt) :
  WhichPkt.decode? which.encode = which := by
  cases which <;> rfl

theorem WhichPkt.encode_decode_flags (which : WhichPkt) (flags : WhichPkt.flagType which) :
  WhichPkt.decodeFlags which (WhichPkt.encodeFlags which flags) = some flags := by
  cases which <;> simp [WhichPkt.encodeFlags, WhichPkt.decodeFlags]
  case publish =>
    have h₁ : BitVec.extractLsb 3 3 (flags.dup ++ flags.qos ++ flags.retain) = flags.dup := by bv_decide
    have h₂ : BitVec.extractLsb 2 1 (flags.dup ++ flags.qos ++ flags.retain) = flags.qos := by bv_decide
    have h₃ : BitVec.extractLsb 0 0 (flags.dup ++ flags.qos ++ flags.retain) = flags.retain := by bv_decide
    rw [h₁, h₂, h₃]
    rfl
  all_goals {
    have : flags.val = _ := flags.property
    simp only [this, BitVec.ofNat_eq_ofNat, exists_true_left]
    exact Subtype.ext flags.property.symm
  }

theorem WhichPkt.roundtrip (which : WhichPkt) (flags : WhichPkt.flagType which) (rest : List UInt8) :
  WhichPkt.parser.run (WhichPkt.serialize which flags ++ rest) = some (⟨which, flags⟩, rest) := by
  simp only [WhichPkt.parser, WhichPkt.serialize,]
  simp only [
    bind_pure_comp, BitVec.append_eq, Nat.reduceAdd, StateT.run_bind,
    StateT.run_monadLift, monadLift_self, Option.pure_def, Option.bind_eq_bind,
    Option.bind, StateT.run_map, Option.map_eq_map
  ]
  simp only [UInt8.roundtrip _ _]
  have : BitVec.extractLsb 7 4 (which.encode ++ which.encodeFlags flags) = which.encode :=
    by bv_decide
  rw [this]
  simp [WhichPkt.encode_decode]
  have : BitVec.extractLsb 3 0 (which.encode ++ which.encodeFlags flags) = which.encodeFlags flags :=
    by bv_decide
  rw [this]
  simp [WhichPkt.encode_decode_flags]

theorem FixedHeader.roundtrip (header : FixedHeader) (rest : List UInt8) :
  FixedHeader.parser.run (header.serialize ++ rest) = some (header, rest) := by
  simp [FixedHeader.parser, FixedHeader.serialize]
  simp [WhichPkt.roundtrip header.which header.flags]
  simp [VarInt.roundtrip _]

end Mqtt
