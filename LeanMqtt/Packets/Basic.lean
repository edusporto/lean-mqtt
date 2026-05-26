import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Packets.VarHeader.Basic
import LeanMqtt.Packets.Payload.Basic

namespace Mqtt

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

structure Packet where
  fixed_header : FixedHeader
  var_header   : VarHeader fixed_header
  payload      : Payload

end Mqtt
