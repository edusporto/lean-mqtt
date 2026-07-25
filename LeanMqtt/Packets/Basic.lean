import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Packets.VarHeader.Basic
import LeanMqtt.Packets.Payload.Basic

namespace Mqtt

/-!
# Top-Level Packets

This module defines the overarching `Header` and `Packet` structures that assemble
the Fixed Header, Variable Header, and Payload into complete MQTT control packets.
-/

/- ========================================================================= -/
/-! ## Header Structure -/

/--
A dependently-typed structure combining a `FixedHeader` and its corresponding
`VarHeader`.
-/
structure Header where
  fh : FixedHeader
  vh : VarHeader fh

def Header.serialize (h : Header) : List UInt8 :=
  FixedHeader.serialize h.fh ++
  VarHeader.serialize h.fh h.vh

def Header.parser : Parser Header := do
  let fh ← FixedHeader.parser
  let vh ← VarHeader.parser fh
  return { fh, vh }

/- ========================================================================= -/
/-! ## Packet Structure -/

/--
The complete representation of an MQTT control packet, combining the headers
with the trailing payload data.
-/
structure Packet where
  fixed_header : FixedHeader
  var_header   : VarHeader fixed_header
  payload      : Payload

end Mqtt
