import LeanMqtt.Serialization.Packets.Packet
import LeanMqtt.Proofs.Packets.FixedHeader
import LeanMqtt.Proofs.Packets.VarHeader

namespace Mqtt

def Header.roundtrip (h : Header) (rest : List UInt8) :
  parser.run (h.serialize ++ rest) = some (h, rest) := by
  simp [parser, serialize]
  simp [FixedHeader.roundtrip]
  simp [VarHeader.roundtrip]

end Mqtt
