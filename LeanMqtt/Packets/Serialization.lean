import LeanMqtt.Serialization
import LeanMqtt.Packets.Packet

namespace Mqtt

-- instance : Serializable FixedHeader where
--   serialize   := FixedHeader.serialize
--   deserialize := FixedHeader.deserialize

def Packet.serialize (p : Packet) : ByteArray :=
  sorry

def Packet.deserialize (b : ByteArray) : Option Packet :=
  sorry

-- instance : Serializable Packet where
--   serialize   := Packet.serialize
--   deserialize := Packet.deserialize

theorem Packet.serialize_roundtrip :
  ∀ p : Packet, deserialize (serialize p) = some header :=
  by sorry

end Mqtt
