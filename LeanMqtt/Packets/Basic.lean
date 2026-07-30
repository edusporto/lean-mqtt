import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Packets.VarHeader.Basic
import LeanMqtt.Packets.Payload.Basic

namespace Mqtt

/-!
# Top-Level Packets

This module defines the overarching `Packet` structure that assembles the Fixed Header,
Variable Header, and Payload into complete MQTT control packets.
-/

/- ========================================================================= -/
/-! ## Packet Structure -/

/--
A raw representation of an MQTT control packet, missing validation of the
`FixedHeader`'s, remaining length (`FixedHeader.remaining_len`).
-/
structure RawPacket where
  fh      : FixedHeader
  vh      : VarHeader fh
  payload : Payload

def RawPacket.serialize (p : RawPacket) : List UInt8 :=
  p.fh.serialize ++ p.vh.serialize p.fh ++ p.payload.serialize

def RawPacket.parser : Parser RawPacket := do
  let fh ← FixedHeader.parser
  let vh ← VarHeader.parser fh
  let payload ← Payload.parser
  return ⟨fh, vh, payload⟩

instance : Codec RawPacket where
  parser := RawPacket.parser
  serialize := RawPacket.serialize

/--
The complete representation of an MQTT control packet, combining the headers
with the trailing payload data, validated to ensure sizes align.
-/
abbrev Packet :=
  PredType RawPacket fun p =>
    [ensure! p.vh.byteSize + p.payload.byteSize = p.fh.remaining_len.val]

def Packet.serialize (p : Packet) : List UInt8 :=
  RawPacket.serialize p.val

def Packet.parser : Parser Packet :=
  PredType.parser _

-- TODO: Future alternative (Option 2):
-- We could consider dependently typing `Payload` directly with its expected length:
-- `structure Payload (len : Nat) where ...`
-- Then we could define `Packet` natively as:
-- `structure Packet where`
-- `  fh : FixedHeader`
-- `  vh : VarHeader fh`
-- `  payload : Payload (fh.size.val - vh.byteSize)`

end Mqtt
