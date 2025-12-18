import LeanMqtt.Primitives
import LeanMqtt.Packets.Packet.FixedHeader
import LeanMqtt.Packets.Packet.VarHeader
import LeanMqtt.Packets.Packet.Payload

namespace Mqtt

structure Header where
  fix : FixedHeader
  var : VarHeader fix

def Header.serialize (h : Header) : List UInt8 :=
  h.fix.serialize ++
  h.var.serialize

def Header.parser : Parser Header := do
  let fix ← FixedHeader.parser
  let var ← VarHeader.parser fix
  return { fix, var }

def Header.roundtrip (h : Header) (rest : List UInt8) :
  parser.run (h.serialize ++ rest) = some (h, rest) := by
  simp [parser, serialize]
  simp [FixedHeader.roundtrip]
  simp [VarHeader.roundtrip]

structure Packet where
  fixed_header : FixedHeader
  var_header   : VarHeader fixed_header
  payload      : Payload

end Mqtt

-- Desafio: depender de coisas para frente
-- Solução: Typestate pattern
