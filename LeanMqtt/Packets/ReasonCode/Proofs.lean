import LeanMqtt.Primitives.UInt.Proofs
import LeanMqtt.Packets.ReasonCode.Basic
import LeanMqtt.Helpers.ParserTactics

namespace Mqtt

theorem ReasonCode.byte_roundtrip (rc : ReasonCode) :
    ReasonCode.decode? (ReasonCode.encode rc) = some rc := by
  cases rc <;> rfl

theorem ReasonCode.byte_reconstruct {rc : ReasonCode} {b : UInt8} :
    ReasonCode.decode? b = some rc → ReasonCode.encode rc = b := by
  unfold decode? encode
  split
  all_goals {
    intro h
    cases h
    try rfl
  }

theorem ReasonCode.roundtrip (rc : ReasonCode) {rest : List UInt8} :
    ReasonCode.parser.run (rc.serialize ++ rest) = some (rc, rest) := by
  simp [ReasonCode.parser, ReasonCode.serialize, ReasonCode.encode, ReasonCode.decode?]
  cases rc <;> rfl

theorem ReasonCode.reconstruct {rc : ReasonCode} {input rest : List UInt8} :
    ReasonCode.parser.run input = some (rc, rest) → input = rc.serialize ++ rest := by
  simp only [ReasonCode.parser, ReasonCode.serialize]
  intro h

  step_parser h → bVal rest1 h_bVal

  finish_parser h → h_rcOpt

  rw [UInt8.reconstruct h_bVal]

  have h_byte_eq := ReasonCode.byte_reconstruct h_rcOpt
  rw [← h_byte_eq]
  rfl

end Mqtt
