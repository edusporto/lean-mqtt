import LeanMqtt.Core.Parser
import LeanMqtt.Defs.Packets.Packet
import LeanMqtt.Serialization.Packets.FixedHeader
import LeanMqtt.Serialization.Packets.VarHeader

namespace Mqtt

def Header.serialize (h : Header) : List UInt8 :=
  FixedHeader.serialize h.fix ++
  VarHeader.serialize h.fix h.var

def Header.parser : Parser Header := do
  let fix ← FixedHeader.parser
  let var ← VarHeader.parser fix
  return { fix, var }

end Mqtt
