import LeanMqtt.Packets.Packet.Basic
import LeanMqtt.Packets.FixedHeader.Proofs
import LeanMqtt.Packets.VarHeader.Proofs

namespace Mqtt

def Header.roundtrip (h : Header) (rest : List UInt8) :
  parser.run (h.serialize ++ rest) = some (h, rest) := by
  simp [parser, serialize]
  simp [FixedHeader.roundtrip]
  simp [VarHeader.roundtrip]

end Mqtt
