import LeanMqtt.Primitives.UInt.Basic
import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Packets.VarHeader.Properties.Basic
import LeanMqtt.Packets.VarHeader.Variations

namespace Mqtt
open Mqtt

/-!
# Variable Header

This module acts as the central router for Variable Headers. It uses dependent types
to dynamically map the parsed `FixedHeader` to the corresponding concrete `VarHeader`
structure based on the packet kind and its specific flags.
-/

/- ========================================================================= -/
/-! ## Variable Header Dispatch -/

/--
Determines the specific Variable Header type based on the Packet Kind
and the specific flags (required for packets like `PUBLISH` which carry QoS).
-/
def VarHeader.getType (kind : PktKind) (flags : PktFlags kind) : Type :=
  match kind, flags with
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

def VarHeader.serializeValue
    {kind : PktKind} {flags : PktFlags kind}
    (value : VarHeader.getType kind flags) : List UInt8 :=
  match kind, flags with
  | .connect, _     => Var_Connect.serialize value
  | .connack, _     => Var_Connack.serialize value
  | .publish, f     => @Var_Publish.serialize f.qos value
  | .puback, _      => Var_Puback.serialize value
  | .pubrec, _      => Var_Pubrec.serialize value
  | .pubrel, _      => Var_Pubrel.serialize value
  | .pubcomp, _     => Var_Pubcomp.serialize value
  | .subscribe, _   => Var_Subscribe.serialize value
  | .suback, _      => Var_Suback.serialize value
  | .unsubscribe, _ => Var_Unsubscribe.serialize value
  | .unsuback, _    => Var_Unsuback.serialize value
  | .pingreq, _     => Var_Pingreq.serialize value
  | .pingresp, _    => Var_Pingresp.serialize value
  | .disconnect, _  => Var_Disconnect.serialize value
  | .auth, _        => Var_Auth.serialize value

def VarHeader.parserValue
    (kind : PktKind) (flags : PktFlags kind)
    : Parser (VarHeader.getType kind flags) :=
  match kind, flags with
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

/--
A dependently-typed abbreviation that automatically resolves to the correct
variable header structure type for a given parsed `FixedHeader`.
-/
abbrev VarHeader (fh : FixedHeader) : Type :=
  VarHeader.getType fh.kind fh.flags

def VarHeader.serialize (fh : FixedHeader) (vh : VarHeader fh) : List UInt8 :=
  VarHeader.serializeValue vh

def VarHeader.parser (fh : FixedHeader) : Parser (VarHeader fh) :=
  VarHeader.parserValue fh.kind fh.flags

end Mqtt
