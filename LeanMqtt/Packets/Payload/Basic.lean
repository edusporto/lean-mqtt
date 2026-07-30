import LeanMqtt.Core.Codec
import LeanMqtt.Core.WithByteSize

namespace Mqtt

/-- The Payload of an MQTT control packet is currently unimplemented. -/
structure Payload where
  -- TODO: Implement Payload variations

def Payload.serialize (_ : Payload) : List UInt8 := []
def Payload.parser : Parser Payload := pure {}

instance : Codec Payload where
  serialize := Payload.serialize
  parser    := Payload.parser

@[simp]
def Payload.byteSize (_ : Payload) : Nat := 0

instance : GetByteSize Payload where
  byteSize := Payload.byteSize

end Mqtt
