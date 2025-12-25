import LeanMqtt.Primitives.Basic
import LeanMqtt.Packets.VarHeader.Properties

namespace Mqtt
open Mqtt

/- ========================= Var_Connect ========================= -/

structure Var_Connect where
  protocol_name    : Str
  protocol_version : UInt8
  connect_flags    : UInt8
  props            : Properties

def Var_Connect.serialize (v : Var_Connect) : List UInt8 :=
  v.protocol_name.serialize ++
  v.protocol_version.serialize ++
  v.connect_flags.serialize ++
  v.props.serialize

def Var_Connect.parser : Parser Var_Connect := do
  let protocol_name ← Str.parser
  let protocol_version ← UInt8.parser
  let connect_flags ← UInt8.parser
  let props ← Properties.parser
  return { protocol_name, protocol_version, connect_flags, props }

/- ========================= Var_Connack ========================= -/

structure Var_Connack where
  ack_flags   : UInt8
  reason_code : UInt8
  props       : Properties

def Var_Connack.serialize (v : Var_Connack) : List UInt8 :=
  v.ack_flags.serialize ++
  v.reason_code.serialize ++
  v.props.serialize

def Var_Connack.parser : Parser Var_Connack := do
  let ack_flags   ← UInt8.parser
  let reason_code ← UInt8.parser
  let props       ← Properties.parser
  return { ack_flags, reason_code, props }

/- ========================= Var_Publish ========================= -/

structure Var_Publish (qos : BitVec 2) where
  topic_name : Str
  packet_id  : if qos > 0 then UInt16 else Unit
  props      : Properties

def Var_Publish.serialize {qos} (v : Var_Publish qos) : List UInt8 :=
  v.topic_name.serialize ++
  (if h : qos > 0 then
    -- We must cast the dependent field to a concrete UInt16 to serialize it
    let pid : UInt16 := cast (by rw [if_pos h]) v.packet_id
    pid.serialize
   else []) ++
  v.props.serialize

def Var_Publish.parser (qos : BitVec 2) : Parser (Var_Publish qos) := do
  let topic_name ← Str.parser

  let packet_id : (if qos > 0 then UInt16 else Unit) ←
    if h : qos > 0 then
      let pid ← UInt16.parser
      pure (cast (by rw [if_pos h]) pid)
    else
      pure (cast (by rw [if_neg h]) ())

  let props ← Properties.parser

  return { topic_name, packet_id, props }

/- ========================= Var_Puback ========================= -/

structure Var_Puback where
  packet_id   : UInt16
  reason_code : UInt8
  -- TODO: dependent on remaining length
  props       : Properties

def Var_Puback.serialize (v : Var_Puback) : List UInt8 :=
  v.packet_id.serialize ++
  v.reason_code.serialize ++
  v.props.serialize

def Var_Puback.parser : Parser (Var_Puback) := do
  let packet_id ← UInt16.parser
  let reason_code ← UInt8.parser
  let props ← Properties.parser
  return { packet_id, reason_code, props }

/- ========================= Var_Pubrec ========================= -/

structure Var_Pubrec where
  packet_id   : UInt16
  reason_code : UInt8
  -- TODO: dependent on remaining length
  props       : Properties

def Var_Pubrec.serialize (v : Var_Pubrec) : List UInt8 :=
  v.packet_id.serialize ++
  v.reason_code.serialize ++
  v.props.serialize

def Var_Pubrec.parser : Parser (Var_Pubrec) := do
  let packet_id ← UInt16.parser
  let reason_code ← UInt8.parser
  let props ← Properties.parser
  return { packet_id, reason_code, props }

/- ========================= Var_Pubrel ========================= -/

structure Var_Pubrel where
  packet_id   : UInt16
  reason_code : UInt8
  props       : Properties

def Var_Pubrel.serialize (v : Var_Pubrel) : List UInt8 :=
  v.packet_id.serialize ++
  v.reason_code.serialize ++
  v.props.serialize

def Var_Pubrel.parser : Parser (Var_Pubrel) := do
  let packet_id ← UInt16.parser
  let reason_code ← UInt8.parser
  let props ← Properties.parser
  return { packet_id, reason_code, props }

/- ========================= Var_Pubcomp ========================= -/

structure Var_Pubcomp where
  packet_id   : UInt16
  reason_code : UInt8
  props       : Properties

def Var_Pubcomp.serialize (v : Var_Pubcomp) : List UInt8 :=
  v.packet_id.serialize ++
  v.reason_code.serialize ++
  v.props.serialize

def Var_Pubcomp.parser : Parser (Var_Pubcomp) := do
  let packet_id ← UInt16.parser
  let reason_code ← UInt8.parser
  let props ← Properties.parser
  return { packet_id, reason_code, props }

/- ========================= Var_Subscribe ========================= -/

structure Var_Subscribe where
  packet_id : UInt16
  props     : Properties

def Var_Subscribe.serialize (v : Var_Subscribe) : List UInt8 :=
  v.packet_id.serialize ++
  v.props.serialize

def Var_Subscribe.parser : Parser (Var_Subscribe) := do
  let packet_id ← UInt16.parser
  let props ← Properties.parser
  return { packet_id, props }

/- ========================= Var_Suback ========================= -/

structure Var_Suback where
  packet_id : UInt16
  props     : Properties

def Var_Suback.serialize (v : Var_Suback) : List UInt8 :=
  v.packet_id.serialize ++
  v.props.serialize

def Var_Suback.parser : Parser (Var_Suback) := do
  let packet_id ← UInt16.parser
  let props ← Properties.parser
  return { packet_id, props }

/- ========================= Var_Unsubscribe ========================= -/

structure Var_Unsubscribe where
  packet_id : UInt16
  props     : Properties

def Var_Unsubscribe.serialize (v : Var_Unsubscribe) : List UInt8 :=
  v.packet_id.serialize ++
  v.props.serialize

def Var_Unsubscribe.parser : Parser (Var_Unsubscribe) := do
  let packet_id ← UInt16.parser
  let props ← Properties.parser
  return { packet_id, props }

/- ========================= Var_Unsuback ========================= -/

structure Var_Unsuback where
  packet_id : UInt16
  props     : Properties

def Var_Unsuback.serialize (v : Var_Unsuback) : List UInt8 :=
  v.packet_id.serialize ++
  v.props.serialize

def Var_Unsuback.parser : Parser (Var_Unsuback) := do
  let packet_id ← UInt16.parser
  let props ← Properties.parser
  return { packet_id, props }

/- ========================= Var_Pingreq ========================= -/

abbrev Var_Pingreq  := Unit

def Var_Pingreq.serialize (_ : Var_Pingreq) : List UInt8 := []
def Var_Pingreq.parser : Parser (Var_Pingreq) := return ()

/- ========================= Var_Pingresp ========================= -/

abbrev Var_Pingresp := Unit

def Var_Pingresp.serialize (_ : Var_Pingresp) : List UInt8 := []
def Var_Pingresp.parser : Parser (Var_Pingresp) := return ()

/- ========================= Var_Disconnect ========================= -/

structure Var_Disconnect where
  reason_code : UInt8
  props       : Properties

def Var_Disconnect.serialize (v : Var_Disconnect) : List UInt8 :=
  v.reason_code.serialize ++
  v.props.serialize

def Var_Disconnect.parser : Parser (Var_Disconnect) := do
  let reason_code ← UInt8.parser
  let props ← Properties.parser
  return { reason_code, props }

/- ========================= Var_Auth ========================= -/

structure Var_Auth where
  reason_code : UInt8
  props       : Properties

def Var_Auth.serialize (v : Var_Auth) : List UInt8 :=
  v.reason_code.serialize ++
  v.props.serialize

def Var_Auth.parser : Parser (Var_Auth) := do
  let reason_code ← UInt8.parser
  let props ← Properties.parser
  return { reason_code, props }

end Mqtt
