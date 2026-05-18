import LeanMqtt.Primitives.Basic
import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Packets.VarHeader.Properties.Basic
import LeanMqtt.Packets.VarHeader.Variations

namespace Mqtt
open Mqtt

/- ========================= VarHeader ========================= -/

/--
  Determines the Variable Header type based on the Packet Kind
  and the specific flags (needed for Publish QoS).
-/
def VarHeader.getType (k : PktKind) (f : PktFlags k) : Type :=
  match k, f with
  | .connect, _     => Var_Connect
  | .connack, _     => Var_Connack
  | .publish, f     => Var_Publish f.qos
  | .puback, _      => Var_Puback
  | .pubrec, _      => Var_Pubrec
  | .pubrel, _      => Var_Pubrel
  | .pubcomp, _     => Var_Pubcomp
  | .subscribe, _   => Var_Subscribe
  | .suback, _      => Var_Suback
  | .unsubscribe, _ => Var_Unsubscribe
  | .unsuback, _    => Var_Unsuback
  | .pingreq, _     => Var_Pingreq
  | .pingresp, _    => Var_Pingresp
  | .disconnect, _  => Var_Disconnect
  | .auth, _        => Var_Auth

def VarHeader.serializeValue {k : PktKind} {f : PktFlags k}
  (v : VarHeader.getType k f) : List UInt8 :=
  match k, f with
  | .connect, _     => Var_Connect.serialize v
  | .connack, _     => Var_Connack.serialize v
  | .publish, f     => @Var_Publish.serialize f.qos v
  | .puback, _      => Var_Puback.serialize v
  | .pubrec, _      => Var_Pubrec.serialize v
  | .pubrel, _      => Var_Pubrel.serialize v
  | .pubcomp, _     => Var_Pubcomp.serialize v
  | .subscribe, _   => Var_Subscribe.serialize v
  | .suback, _      => Var_Suback.serialize v
  | .unsubscribe, _ => Var_Unsubscribe.serialize v
  | .unsuback, _    => Var_Unsuback.serialize v
  | .pingreq, _     => Var_Pingreq.serialize v
  | .pingresp, _    => Var_Pingresp.serialize v
  | .disconnect, _  => Var_Disconnect.serialize v
  | .auth, _        => Var_Auth.serialize v

def VarHeader.parserValue
  (k : PktKind) (f : PktFlags k) : Parser (VarHeader.getType k f) :=
  match k, f with
  | .connect, _     => Var_Connect.parser
  | .connack, _     => Var_Connack.parser
  | .publish, f     => Var_Publish.parser f.qos
  | .puback, _      => Var_Puback.parser
  | .pubrec, _      => Var_Pubrec.parser
  | .pubrel, _      => Var_Pubrel.parser
  | .pubcomp, _     => Var_Pubcomp.parser
  | .subscribe, _   => Var_Subscribe.parser
  | .suback, _      => Var_Suback.parser
  | .unsubscribe, _ => Var_Unsubscribe.parser
  | .unsuback, _    => Var_Unsuback.parser
  | .pingreq, _     => Var_Pingreq.parser
  | .pingresp, _    => Var_Pingresp.parser
  | .disconnect, _  => Var_Disconnect.parser
  | .auth, _        => Var_Auth.parser

abbrev VarHeader (h : FixedHeader) : Type :=
  VarHeader.getType h.kind h.flags

def VarHeader.serialize (h : FixedHeader) (v : VarHeader h) : List UInt8 :=
  VarHeader.serializeValue v

def VarHeader.parser (h : FixedHeader) : Parser (VarHeader h) :=
  VarHeader.parserValue h.kind h.flags

end Mqtt
