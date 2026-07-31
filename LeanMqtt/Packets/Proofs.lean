import LeanMqtt.Packets.Basic
import LeanMqtt.Packets.FixedHeader.Proofs
import LeanMqtt.Packets.VarHeader.Proofs
import LeanMqtt.Packets.Payload.Proofs
import LeanMqtt.Helpers.ParserTactics

namespace Mqtt

theorem RawPacket.roundtrip (p : RawPacket) {rest : List UInt8} :
    RawPacket.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp [RawPacket.parser, RawPacket.serialize]
  simp [FixedHeader.roundtrip]
  simp [VarHeader.roundtrip]
  simp [Payload.roundtrip]
  exact ⟨{}, trivial⟩

theorem RawPacket.reconstruct {p : RawPacket} {input rest : List UInt8} :
    RawPacket.parser.run input = some (p, rest) → input = p.serialize ++ rest := by
  simp only [RawPacket.parser, RawPacket.serialize]
  intro h_run

  step_parser h_run → fixVal rest1 h_fixVal
  step_parser h_run → varVal rest2 h_varVal
  step_parser h_run → payloadVal rest3 h_payloadVal

  finish_parser h_run → h_eq

  cases h_eq

  have h_fix_rec := FixedHeader.reconstruct h_fixVal
  have h_var_rec := VarHeader.reconstruct h_varVal
  have h_payload_rec := Payload.reconstruct h_payloadVal

  rw [h_fix_rec, h_var_rec, h_payload_rec]

  simp only [List.append_assoc]

instance : LawfulCodec RawPacket where
  roundtrip := RawPacket.roundtrip
  reconstruct := RawPacket.reconstruct

theorem RawPacket.serialize_len (p : RawPacket) :
    p.serialize.length = GetByteSize.byteSize p := by
  simp only [RawPacket.serialize, GetByteSize.byteSize, RawPacket.byteSize]
  simp only [List.length_append]
  simp only [FixedHeader.serialize_len p.fh,
    VarHeader.serialize_len p.vh,
    Payload.serialize_len p.pl]
  rfl

instance : LawfulByteSize RawPacket where
  serialize_len := RawPacket.serialize_len

theorem Packet.roundtrip (p : Packet) {rest : List UInt8} :
    Packet.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp [Packet.parser, Packet.serialize]
  exact PredType.roundtrip p

theorem Packet.reconstruct {p : Packet} {input rest : List UInt8} :
    Packet.parser.run input = some (p, rest) → input = p.serialize ++ rest := by
  simp only [Packet.parser, Packet.serialize]
  intro h
  exact PredType.reconstruct _ h

theorem Packet.serialize_len (p : Packet) :
    (Packet.serialize p).length = GetByteSize.byteSize p := by
  exact PredType.serialize_len p

instance : LawfulByteSize Packet where
  serialize_len := Packet.serialize_len

end Mqtt
