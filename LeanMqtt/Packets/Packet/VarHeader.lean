import LeanMqtt.Primitives
import LeanMqtt.Packets.Packet.FixedHeader

namespace Mqtt

/--
  Defines the type of the value stored in a property.

  We do a three layer approach (ID -> Kind -> Type) instead of deriving
  types directly from the ID to help Lean automatically decide the type of
  each property in `Property.serializeKind`, without having to include
  proofs in each branch.
-/
inductive Property.Kind
  | u8 | u16 | u32 | varInt | binary | string | pair | none
  deriving DecidableEq

def Property.getKind (id : VarInt) : Property.Kind :=
  match id with
  |  1 | 23 | 25 | 36 | 37 | 40 | 41 | 42 => .u8
  | 19 | 33 | 34 | 35                     => .u16
  |  2 | 17 | 24 | 39                     => .u32
  | 11                                    => .varInt
  |  9 | 22                               => .binary
  |  3 |  8 | 18 | 21 | 26 | 28 | 31      => .string
  | 38                                    => .pair
  | _                                     => .none

abbrev Property.typeOfKind (k : Property.Kind) : Type :=
  match k with
  | .u8     => UInt8
  | .u16    => UInt16
  | .u32    => UInt32
  | .varInt => VarInt
  | .binary => BinaryData
  | .string => Str
  | .pair   => StrPair
  | .none   => Empty

abbrev Property.valType (id : VarInt) : Type :=
  Property.typeOfKind (getKind id)

structure Property where
  id  : VarInt
  val : Property.valType id

/--
  Serializes the value stored in a property from its kind.

  We pass `k`, and `val` of type `Property.typeOfKind k` to help Lean automatically
  reduce the type of `val` to what's desired in each branch.
-/
def Property.serializeKind (k : Property.Kind) (val : Property.typeOfKind k) : List UInt8 :=
  match k with
  | .u8     => val.serialize
  | .u16    => val.serialize
  | .u32    => val.serialize
  | .varInt => val.serialize
  | .binary => val.serialize
  | .string => val.serialize
  | .pair   => val.serialize
  | .none   => nomatch val

def Property.parserKind (k : Property.Kind) : Parser (Property.typeOfKind k) :=
  match k with
  | .u8     => UInt8.parser
  | .u16    => UInt16.parser
  | .u32    => UInt32.parser
  | .varInt => VarInt.parser
  | .binary => BinaryData.parser
  | .string => Str.parser
  | .pair   => StrPair.parser
  | .none   => none

def Property.roundtrip_kind (k : Property.Kind) (val : Property.typeOfKind k) :
  (Property.parserKind k).run (Property.serializeKind k val ++ rest) = some (val, rest) := by
  simp [Property.parserKind, Property.serializeKind]
  split
  repeat' simp only
  · simp only [UInt8.roundtrip]
  · simp only [UInt16.roundtrip]
  · simp only [UInt32.roundtrip]
  · simp only [VarInt.roundtrip]
  · simp only [BinaryData.roundtrip]
  · simp only [Str.roundtrip]
  · simp only [StrPair.roundtrip]
  · contradiction

def Property.serialize (p : Property) : List UInt8 :=
  p.id.serialize ++ Property.serializeKind (getKind p.id) p.val

def Property.parser : Parser Property := do
  let id ← VarInt.parser
  let kind := Property.getKind id
  let val ← Property.parserKind kind
  return { id, val }

theorem Property.roundtrip (p : Property) (rest : List UInt8) :
  Property.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp [Property.parser, Property.serialize]
  simp [Option.bind, Option.map]
  simp [VarInt.roundtrip]
  simp [Property.roundtrip_kind]

@[simp]
def Property.byteSize (p : Property) : Nat :=
  p.serialize.length

instance : GetLength (List Property) where
  length l := l.foldl (fun acc p => acc + p.byteSize) 0

abbrev Properties := WithLength (List Property) VarInt

def Properties.serialize (ps : Properties) : List UInt8 :=
  VarInt.serialize ps.len ++
  ps.val.foldl (fun acc p => acc ++ p.serialize) []

def parsePropsLoop (input : List UInt8) : Option (List Property) :=
  if /-h_empty :-/ input.isEmpty then
    some []
  else
    -- Run the parser manually on the current list
    match Property.parser.run input with
    | some (p, rest) =>
      -- CRITICAL: We explicitly check that the parser consumed at least 1 byte.
      -- This guarantees 'rest' is strictly smaller than 'input'.
      -- TODO: we may be able to derive this check instead performing it
      if /-h_progress :-/ rest.length < input.length then
        match parsePropsLoop rest with
        | some tail => some (p :: tail)
        | none      => none
      else
        -- Parser succeeded but consumed 0 bytes (infinite loop risk).
        -- Treat as an error.
        none
    | none => none
termination_by input.length

-- TODO: prove
theorem parsePropsLoop_len (chunk : List UInt8) (l : List Property) :
  parsePropsLoop chunk = some l → chunk.length = GetLength.length l := by
  simp [GetLength.length]
  sorry

def Properties.parser : Parser Properties := do
  -- 1. Parse the Length Prefix
  let len ← VarInt.parser
  let ⟨chunk, h_chunk_len⟩ ← bytesParserWithProof len

  match h_parsed : parsePropsLoop chunk with
  | some props =>
    have h_len : len = GetLength.length props := by
      rw [←h_chunk_len]
      exact parsePropsLoop_len _ _ h_parsed

    return { val := props, len := ⟨len, h_len⟩ }
  | none => none

theorem Properties.roundtrip (ps : Properties) (rest : List UInt8) :
  Properties.parser.run (ps.serialize ++ rest) = some (ps, rest) := by
  sorry

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

def Var_Connect.roundtrip (v : Var_Connect) (rest : List UInt8) :
  Var_Connect.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Connect.parser, Var_Connect.serialize]
  simp [Str.roundtrip]
  simp [UInt8.roundtrip]
  simp [Properties.roundtrip]

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

theorem Var_Connack.roundtrip (v : Var_Connack) (rest : List UInt8) :
  Var_Connack.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Connack.parser, Var_Connack.serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

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

-- def Var_Publish.parser' (qos : BitVec 2) : Parser (Var_Publish qos) := do
--   let topic_name ← Str.parser
--   let packet_id : (if qos > 0 then UInt16 else Unit) ←
--     if h : qos > 0 then
--       let pid ← UInt16.parser
--       have h_type : UInt16 = (if qos > 0 then UInt16 else Unit) := by rw [if_pos h]
--       pure (h_type ▸ pid)
--     else
--       have h_type : Unit = (if qos > 0 then UInt16 else Unit) := by rw [if_neg h]
--       pure (h_type ▸ ())
--   let props ← Properties.parser
--   return { topic_name, packet_id, props }

theorem Var_Publish.roundtrip {qos} (v : Var_Publish qos) (rest : List UInt8) :
  (Var_Publish.parser qos).run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Publish.parser, Var_Publish.serialize]
  simp [Str.roundtrip]

  split
  · next h_qos =>
    -- Case: QoS > 0
    simp [UInt16.roundtrip]
    simp [Properties.roundtrip]
  · next h_qos =>
    -- Case: QoS == 0
    simp [Properties.roundtrip]
    congr
    have h_zero : qos = 0 := by bv_decide
    subst h_zero
    simp
    apply Subsingleton.elim () v.packet_id

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

theorem Var_Puback.roundtrip (v : Var_Puback) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Puback.parser, Var_Puback.serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

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

theorem Var_Pubrec.roundtrip (v : Var_Pubrec) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

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

theorem Var_Pubrel.roundtrip (v : Var_Pubrel) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

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

theorem Var_Pubcomp.roundtrip (v : Var_Pubcomp) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

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

theorem Var_Subscribe.roundtrip (v : Var_Subscribe) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

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

theorem Var_Suback.roundtrip (v : Var_Suback) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

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

theorem Var_Unsubscribe.roundtrip (v : Var_Unsubscribe) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

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

theorem Var_Unsuback.roundtrip (v : Var_Unsuback) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

abbrev Var_Pingreq  := Unit

def Var_Pingreq.serialize (_ : Var_Pingreq) : List UInt8 := []
def Var_Pingreq.parser : Parser (Var_Pingreq) := return ()
theorem Var_Pingreq.roundtrip (v : Var_Pingreq) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]

abbrev Var_Pingresp := Unit

def Var_Pingresp.serialize (_ : Var_Pingresp) : List UInt8 := []
def Var_Pingresp.parser : Parser (Var_Pingresp) := return ()
theorem Var_Pingresp.roundtrip (v : Var_Pingresp) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]

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

theorem Var_Disconnect.roundtrip (v : Var_Disconnect) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

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

theorem Var_Auth.roundtrip (v : Var_Auth) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

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

theorem VarHeader.roundtrip_value
  {w : WhichPkt} {f : WhichPkt.flagType w} (v : VarHeader.getType w f) :
  (VarHeader.parserValue w f).run (VarHeader.serializeValue v ++ rest) = some (v, rest) := by
  simp [parserValue, serializeValue]
  split
  repeat' simp only
  · simp [Var_Connect.roundtrip _ _]
  · simp [Var_Connack.roundtrip _ _]
  · simp [Var_Publish.roundtrip _ _]
  · simp [Var_Puback.roundtrip _ _]
  · simp [Var_Pubrec.roundtrip _ _]
  · simp [Var_Pubrel.roundtrip _ _]
  · simp [Var_Pubcomp.roundtrip _ _]
  · simp [Var_Subscribe.roundtrip _ _]
  · simp [Var_Suback.roundtrip _ _]
  · simp [Var_Unsubscribe.roundtrip _ _]
  · simp [Var_Unsuback.roundtrip _ _]
  · simp [Var_Pingreq.roundtrip _ _]
  · simp [Var_Pingresp.roundtrip _ _]
  · simp [Var_Disconnect.roundtrip _ _]
  · simp [Var_Auth.roundtrip _ _]


def VarHeader.serialize (h : FixedHeader) (v : VarHeader h) : List UInt8 :=
  VarHeader.serializeValue v

def VarHeader.parser (h : FixedHeader) : Parser (VarHeader h) :=
  VarHeader.parserValue h.which h.flags

theorem VarHeader.roundtrip (h : FixedHeader) (v : VarHeader h) (rest : List UInt8) :
  (parser h).run (v.serialize h ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [VarHeader.roundtrip_value v]

end Mqtt

/-
-- TODO: explore these encodings for VarHeader and Property

inductive VarHeader : PacketType -> Type
  | connect : String -> UInt8 ->
              UInt8 -> Properties ->
              VarHeader .CONNECT
  | publish : String ->
              (qos : QoS) ->
              (qos > 0 -> UInt16) ->
              Properties ->
              VarHeader .PUBLISH
  | ...

inductive Property
  | sessionExpiryInterval : UInt32 ->
                            Property
  | receiveMaximum : UInt16 -> Property
  | ...
-/
