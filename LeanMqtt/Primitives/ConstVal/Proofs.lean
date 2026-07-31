import LeanMqtt.Core.Codec
import LeanMqtt.Primitives.ConstVal.Basic
import LeanMqtt.Helpers.ParserTactics

namespace Mqtt
open Mqtt

theorem ConstVal.roundtrip {α : Type} [c : Codec α] [LawfulCodec α] [DecidableEq α]
    (expected : α) (v : ConstVal α expected) {rest : List UInt8} :
    (ConstVal.parser expected).run (ConstVal.serialize v ++ rest) = some (v, rest) := by
  unfold ConstVal.parser ConstVal.serialize
  cases v with
  | mk val property =>
    have h_round := @LawfulCodec.roundtrip α c _ val rest
    dsimp [bind, StateT.bind, Option.bind, StateT.run] at *
    rw [h_round]
    dsimp
    rw [dif_pos property]
    rfl

theorem ConstVal.reconstruct {α : Type} [c : Codec α] [LawfulCodec α] [DecidableEq α]
    (expected : α) {v : ConstVal α expected} {input rest : List UInt8} :
    (ConstVal.parser expected).run input = some (v, rest) → input = ConstVal.serialize v ++ rest := by
  unfold ConstVal.parser ConstVal.serialize
  intro h
  step_parser h → val rest' h_val
  split at h
  · finish_parser h → h_eq
    subst h_eq
    apply @LawfulCodec.reconstruct α c _ val input
    exact h_val
  · dsimp [failure, Alternative.failure, StateT.failure, Option.bind] at h
    contradiction

theorem ConstVal.serialize_len {α : Type} [Codec α] [GetByteSize α] {expected : α}
    (v : ConstVal α expected) [LawfulByteSize α] :
    (ConstVal.serialize v).length = GetByteSize.byteSize v := by
  exact LawfulByteSize.serialize_len v.val

instance {α : Type} {expected : α}
    [Codec α] [LawfulCodec α] [DecidableEq α] : LawfulCodec (ConstVal α expected) where
  roundtrip := ConstVal.roundtrip expected
  reconstruct := ConstVal.reconstruct expected

instance {α : Type} {expected : α}
    [Codec α] [GetByteSize α] [LawfulCodec α] [LawfulByteSize α] [DecidableEq α] :
    LawfulByteSize (ConstVal α expected) where
  serialize_len := fun v => ConstVal.serialize_len v

end Mqtt
