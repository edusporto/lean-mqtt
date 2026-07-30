import LeanMqtt.Packets.Payload.Basic
import LeanMqtt.Helpers.ParserTactics

namespace Mqtt
open Mqtt

-- TODO: Revisit these proofs when Payload is properly implemented

theorem Payload.roundtrip (p : Payload) {rest : List UInt8} :
    Payload.parser.run (p.serialize ++ rest) = some (p, rest) := by
  cases p
  rfl

theorem Payload.reconstruct {p : Payload} {input rest : List UInt8} :
    Payload.parser.run input = some (p, rest) →
    input = p.serialize ++ rest := by
  intro h
  cases p
  simp [Payload.parser] at h
  simp [Payload.serialize]
  exact h

theorem Payload.serialize_len (p : Payload) :
    p.serialize.length = GetByteSize.byteSize p := by
  cases p
  rfl

end Mqtt
