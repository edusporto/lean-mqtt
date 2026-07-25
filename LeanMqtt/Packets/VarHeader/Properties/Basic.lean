import LeanMqtt.Primitives.SizedList.Basic
import LeanMqtt.Packets.VarHeader.Property.Basic
import LeanMqtt.Packets.VarHeader.Property.Proofs

namespace Mqtt
open Mqtt

/-!
# Properties Collection

This module defines the `Properties` type, which represents a collection of
MQTT properties prefixed by their total byte length.
-/

/- ========================================================================= -/
/-! ## Properties Structure -/

/--
A `SizedList` of `Property` elements, prefixed by a `VarInt` denoting the total
byte length of the serialized properties.
-/
abbrev Properties := SizedList Property VarInt

def Properties.serialize (ps : Properties) : List UInt8 :=
  SizedList.serialize ps

def Properties.parser : Parser Properties :=
  SizedList.parser

end Mqtt
