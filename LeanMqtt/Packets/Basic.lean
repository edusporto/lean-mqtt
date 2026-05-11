import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Packets.VarHeader.Basic
import LeanMqtt.Packets.Payload.Basic

namespace Mqtt

structure Header where
  fix : FixedHeader
  var : VarHeader fix

def Header.serialize (h : Header) : List UInt8 :=
  FixedHeader.serialize h.fix ++
  VarHeader.serialize h.fix h.var

def Header.parser : Parser Header := do
  let fix ← FixedHeader.parser
  let var ← VarHeader.parser fix
  return { fix, var }

structure Packet where
  fixed_header : FixedHeader
  var_header   : VarHeader fixed_header
  payload      : Payload

end Mqtt
