import LeanMqtt.Defs.Packets.FixedHeader
import LeanMqtt.Defs.Packets.Properties

namespace Mqtt

structure Var_Connect where
  protocol_name    : Str
  protocol_version : UInt8
  connect_flags    : UInt8
  props            : Properties

structure Var_Connack where
  ack_flags   : UInt8
  reason_code : UInt8
  props       : Properties

structure Var_Publish (qos : BitVec 2) where
  topic_name : Str
  packet_id  : if qos > 0 then UInt16 else Unit
  props      : Properties

structure Var_Puback where
  packet_id   : UInt16
  reason_code : UInt8
  -- TODO: dependent on remaining length
  props       : Properties

structure Var_Pubrec where
  packet_id   : UInt16
  reason_code : UInt8
  -- TODO: dependent on remaining length
  props       : Properties

structure Var_Pubrel where
  packet_id   : UInt16
  reason_code : UInt8
  props       : Properties

structure Var_Pubcomp where
  packet_id   : UInt16
  reason_code : UInt8
  props       : Properties

structure Var_Subscribe where
  packet_id : UInt16
  props     : Properties

structure Var_Suback where
  packet_id : UInt16
  props     : Properties

structure Var_Unsubscribe where
  packet_id : UInt16
  props     : Properties

structure Var_Unsuback where
  packet_id : UInt16
  props     : Properties

abbrev Var_Pingreq  := Unit
abbrev Var_Pingresp := Unit

structure Var_Disconnect where
  reason_code : UInt8
  props       : Properties

structure Var_Auth where
  reason_code : UInt8
  props       : Properties

/--
  Determines the Variable Header type based on the Packet Kind
  and the specific flags (needed for Publish QoS).
-/
def VarHeader.getType (w : WhichPkt) (f : WhichPkt.flagType w) : Type :=
  match w with
  | .connect     => Var_Connect
  | .connack     => Var_Connack
  | .publish     => Var_Publish f.qos
  | .puback      => Var_Puback
  | .pubrec      => Var_Pubrec
  | .pubrel      => Var_Pubrel
  | .pubcomp     => Var_Pubcomp
  | .subscribe   => Var_Subscribe
  | .suback      => Var_Suback
  | .unsubscribe => Var_Unsubscribe
  | .unsuback    => Var_Unsuback
  | .pingreq     => Var_Pingreq
  | .pingresp    => Var_Pingresp
  | .disconnect  => Var_Disconnect
  | .auth        => Var_Auth

abbrev VarHeader (h : FixedHeader) : Type :=
  VarHeader.getType h.which h.flags

end Mqtt
