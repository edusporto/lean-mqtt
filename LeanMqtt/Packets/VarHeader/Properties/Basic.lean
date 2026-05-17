import LeanMqtt.Primitives.SizedList.Basic
import LeanMqtt.Packets.VarHeader.Property.Basic
import LeanMqtt.Packets.VarHeader.Property.Proofs

namespace Mqtt
open Mqtt

/- ========================= Properties ========================= -/

abbrev Properties := SizedList Property VarInt

def Properties.serialize (ps : Properties) : List UInt8 :=
  SizedList.serialize ps

def Properties.parser : Parser Properties :=
  SizedList.parser

end Mqtt
