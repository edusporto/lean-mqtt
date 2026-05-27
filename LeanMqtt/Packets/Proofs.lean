import LeanMqtt.Packets.Basic
import LeanMqtt.Packets.FixedHeader.Proofs
import LeanMqtt.Packets.VarHeader.Proofs

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

  obtain ⟨fix, m1, h_fix, h_next⟩ := Parser.bind_run_success h_run
  obtain ⟨var, m2, h_var, h_pure⟩ := Parser.bind_run_success h_next

  obtain ⟨h_eq, h_rest_eq⟩ := Parser.pure_run_success h_pure
  subst h_rest_eq

  cases h_eq

  have h_fix_rec := FixedHeader.reconstruct h_fix
  have h_var_rec := VarHeader.reconstruct h_var

  rw [h_fix_rec, h_var_rec]

  simp only [List.append_assoc]

end Mqtt
