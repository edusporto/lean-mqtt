import LeanMqtt.Primitives.UInt.Proofs
import LeanMqtt.Packets.ReasonCode.Basic

namespace Mqtt

theorem GlobalReasonCode.byte_roundtrip (rc : GlobalReasonCode) :
    GlobalReasonCode.decode? (rc.encode) = some rc := by
  cases rc <;> rfl

theorem GlobalReasonCode.byte_reconstruct {rc : GlobalReasonCode} {b : UInt8} :
    GlobalReasonCode.decode? b = some rc → rc.encode = b := by
  unfold decode? encode
  split
  all_goals {
    intro h
    cases h
    try rfl
  }

theorem GlobalReasonCode.roundtrip (rc : GlobalReasonCode) {rest : List UInt8} :
    GlobalReasonCode.parser.run (rc.serialize ++ rest) = some (rc, rest) := by
  simp [GlobalReasonCode.parser, GlobalReasonCode.serialize, GlobalReasonCode.encode, GlobalReasonCode.decode?]
  cases rc <;> rfl

theorem GlobalReasonCode.reconstruct {rc : GlobalReasonCode} {input rest : List UInt8} :
    GlobalReasonCode.parser.run input = some (rc, rest) → input = rc.serialize ++ rest := by
  simp only [GlobalReasonCode.parser, GlobalReasonCode.serialize]
  intro h

  step_parser h → bVal rest1 h_bVal

  finish_parser h → h_rcOpt

  rw [UInt8.reconstruct h_bVal]

  have h_byte_eq := GlobalReasonCode.byte_reconstruct h_rcOpt
  rw [← h_byte_eq]
  rfl

theorem ReasonCode.roundtrip {p : PktKind} (prc : ReasonCode p) {rest : List UInt8} :
    (ReasonCode.parser p).run (prc.serialize ++ rest) = some (prc, rest) := by
  simp [ReasonCode.parser, ReasonCode.serialize]
  have h_rc := GlobalReasonCode.roundtrip prc.val (rest := rest)
  simp [h_rc]
  have h_valid : isValidReasonCode p prc.val = true := prc.property
  split
  · next h_eq =>
    congr
  · next h_neq =>
    contradiction

theorem ReasonCode.reconstruct {p : PktKind} {prc : ReasonCode p} {input rest : List UInt8} :
    (ReasonCode.parser p).run input = some (prc, rest) → input = prc.serialize ++ rest := by
  intro h
  simp only [ReasonCode.parser, ReasonCode.serialize] at *

  step_parser h → rcVal rest1 h_rcVal

  split at h
  · next h_valid =>
    simp [pure] at h
    injection h with h_pair
    injection h_pair with h_prc_eq h_rest_eq
    subst h_rest_eq
    have h_rc_eq : prc.val = rcVal := by rw [← h_prc_eq]
    subst h_rc_eq

    exact GlobalReasonCode.reconstruct h_rcVal
  · next h_invalid =>
    contradiction

end Mqtt
