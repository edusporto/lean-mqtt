import LeanMqtt.Packets.Basic
import LeanMqtt.Packets.FixedHeader.Proofs
import LeanMqtt.Packets.VarHeader.Proofs
import LeanMqtt.Helpers.ParserTactics

namespace Mqtt

def Header.roundtrip (h : Header) {rest : List UInt8} :
    Header.parser.run (h.serialize ++ rest) = some (h, rest) := by
  simp [parser, serialize]
  simp [FixedHeader.roundtrip]
  simp [VarHeader.roundtrip]

theorem Header.reconstruct {h : Header} {input rest : List UInt8} :
    Header.parser.run input = some (h, rest) → input = h.serialize ++ rest := by

  simp only [parser, serialize]
  intro h_run

  step_parser h_run → fixVal rest1 h_fixVal
  step_parser h_run → varVal rest2 h_varVal

  finish_parser h_run → h_eq

  cases h_eq

  have h_fix_rec := FixedHeader.reconstruct h_fixVal
  have h_var_rec := VarHeader.reconstruct h_varVal

  rw [h_fix_rec, h_var_rec]

  simp only [List.append_assoc]

end Mqtt
