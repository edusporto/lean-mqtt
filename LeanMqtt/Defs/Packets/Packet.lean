import LeanMqtt.Defs.Packets.FixedHeader
import LeanMqtt.Defs.Packets.VarHeader
import LeanMqtt.Defs.Packets.Payload

namespace Mqtt

structure Header where
  fix : FixedHeader
  var : VarHeader fix

structure Packet where
  fixed_header : FixedHeader
  var_header   : VarHeader fixed_header
  payload      : Payload

end Mqtt
