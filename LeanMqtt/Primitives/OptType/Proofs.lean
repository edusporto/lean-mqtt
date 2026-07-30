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
    (v : OptType α b) (h_len : ∀ a : α, (Codec.serialize a).length = GetByteSize.byteSize a) :
    (OptType.serialize b v).length = GetByteSize.byteSize v := by
  match b, v with
  | true, val => exact h_len val
  | false, () => rfl

end Mqtt
