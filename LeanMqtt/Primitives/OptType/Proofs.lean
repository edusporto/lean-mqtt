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
