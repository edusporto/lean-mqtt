import LeanMqtt.Primitives.PredType.Basic
import LeanMqtt.Helpers.ParserTactics

namespace Mqtt
open Mqtt

theorem PredType.roundtrip {α : Type} [c : Codec α] [LawfulCodec α] {gen : α → List Condition}
    (v : PredType α gen) {rest : List UInt8} :
    (PredType.parser gen).run (PredType.serialize v ++ rest) = some (v, rest) := by
  unfold PredType.parser PredType.serialize
  cases v with
  | mk val property =>
    have h_round := @LawfulCodec.roundtrip α c _ val rest
    dsimp [bind, StateT.bind, Option.bind, StateT.run] at *
    rw [h_round]
    dsimp
    rw [dif_pos property]
    rfl

theorem PredType.reconstruct {α : Type} [c : Codec α] [LawfulCodec α] (gen : α → List Condition)
    {v : PredType α gen} {input rest : List UInt8} :
    (PredType.parser gen).run input = some (v, rest) → input = PredType.serialize v ++ rest := by
  unfold PredType.parser PredType.serialize
  intro h
  step_parser h → val rest' h_val
  split at h
  · finish_parser h → h_eq
    subst h_eq
    apply @LawfulCodec.reconstruct α c _ val input
    exact h_val
  · dsimp [failure, Alternative.failure, StateT.failure, Option.bind] at h
    contradiction

end Mqtt
