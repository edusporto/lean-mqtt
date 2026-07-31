import LeanMqtt.Core.Codec
import LeanMqtt.Primitives.OptType.Basic

namespace Mqtt
open Mqtt

theorem OptType.roundtrip {α : Type} [c : Codec α] [LawfulCodec α] (b : Bool) (v : OptType α b) {rest : List UInt8} :
    (OptType.parser b).run (serialize b v ++ rest) = some (v, rest) := by
  match b, v with
  | true,  val =>
    exact @LawfulCodec.roundtrip α c _ val rest
  | false, ()  =>
    rfl

theorem OptType.reconstruct {α : Type} [c : Codec α] [LawfulCodec α]
    (b : Bool) {v : OptType α b} {input rest : List UInt8} :
    (OptType.parser b).run input = some (v, rest) → input = serialize b v ++ rest := by
  intro h
  match b, v, h with
  | true, val, h =>
    exact @LawfulCodec.reconstruct α c _ val input rest h
  | false, (), h =>
    injection h with h_pair
    injection h_pair with _ _

theorem OptType.serialize_len {α : Type} [Codec α] [GetByteSize α] {b : Bool}
    (v : OptType α b) [LawfulByteSize α] :
    (OptType.serialize b v).length = GetByteSize.byteSize v := by
  match b, v with
  | true, val =>
    exact @LawfulByteSize.serialize_len α _ _ _ val
  | false, () => rfl

instance {α : Type} {b : Bool} [Codec α] [LawfulCodec α] : LawfulCodec (OptType α b) where
  roundtrip := OptType.roundtrip b
  reconstruct := OptType.reconstruct b

instance {α : Type} {b : Bool}
    [Codec α] [GetByteSize α] [LawfulCodec α] [LawfulByteSize α] :
    LawfulByteSize (OptType α b) where
  serialize_len := fun v => OptType.serialize_len v

end Mqtt
