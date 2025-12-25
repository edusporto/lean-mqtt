import LeanMqtt.Primitives.Basic
import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Packets.VarHeader.Properties
import LeanMqtt.Packets.VarHeader.Variations

namespace Mqtt
open Mqtt

/- ========================= VarHeader ========================= -/

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

def VarHeader.serializeValue {w : WhichPkt} {f : WhichPkt.flagType w}
  (v : VarHeader.getType w f) : List UInt8 :=
  match w with
  | .connect     => Var_Connect.serialize v
  | .connack     => Var_Connack.serialize v
  | .publish     => @Var_Publish.serialize f.qos v
  | .puback      => Var_Puback.serialize v
  | .pubrec      => Var_Pubrec.serialize v
  | .pubrel      => Var_Pubrel.serialize v
  | .pubcomp     => Var_Pubcomp.serialize v
  | .subscribe   => Var_Subscribe.serialize v
  | .suback      => Var_Suback.serialize v
  | .unsubscribe => Var_Unsubscribe.serialize v
  | .unsuback    => Var_Unsuback.serialize v
  | .pingreq     => Var_Pingreq.serialize v
  | .pingresp    => Var_Pingresp.serialize v
  | .disconnect  => Var_Disconnect.serialize v
  | .auth        => Var_Auth.serialize v

def VarHeader.parserValue (w : WhichPkt) (f : WhichPkt.flagType w) : Parser (VarHeader.getType w f) :=
  match w with
  | .connect     => Var_Connect.parser
  | .connack     => Var_Connack.parser
  | .publish     => Var_Publish.parser f.qos
  | .puback      => Var_Puback.parser
  | .pubrec      => Var_Pubrec.parser
  | .pubrel      => Var_Pubrel.parser
  | .pubcomp     => Var_Pubcomp.parser
  | .subscribe   => Var_Subscribe.parser
  | .suback      => Var_Suback.parser
  | .unsubscribe => Var_Unsubscribe.parser
  | .unsuback    => Var_Unsuback.parser
  | .pingreq     => Var_Pingreq.parser
  | .pingresp    => Var_Pingresp.parser
  | .disconnect  => Var_Disconnect.parser
  | .auth        => Var_Auth.parser

abbrev VarHeader (h : FixedHeader) : Type :=
  VarHeader.getType h.which h.flags

def VarHeader.serialize (h : FixedHeader) (v : VarHeader h) : List UInt8 :=
  VarHeader.serializeValue v

def VarHeader.parser (h : FixedHeader) : Parser (VarHeader h) :=
  VarHeader.parserValue h.which h.flags

end Mqtt
