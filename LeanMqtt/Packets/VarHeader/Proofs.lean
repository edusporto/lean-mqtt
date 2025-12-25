import LeanMqtt.Packets.VarHeader.Basic
import LeanMqtt.Packets.VarHeader.Properties
import LeanMqtt.Packets.VarHeader.Variations
import LeanMqtt.Primitives.Proofs

namespace Mqtt
open Mqtt

def Property.roundtrip_kind (k : Property.Kind) (val : Property.typeOfKind k) (rest : List UInt8) :
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

theorem Property.roundtrip (p : Property) (rest : List UInt8) :
  Property.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp [Property.parser, Property.serialize]
  simp [Option.bind, Option.map]
  simp [VarInt.roundtrip]
  simp [Property.roundtrip_kind]

-- TODO: prove
theorem parsePropsLoop_len (chunk : List UInt8) (l : List Property) :
  parsePropsLoop chunk = some l → chunk.length = (l.foldl (fun acc p => acc + p.byteSize) 0) := by
  -- simp [GetLength.length]
  sorry

theorem Properties.roundtrip (ps : Properties) (rest : List UInt8) :
  Properties.parser.run (ps.serialize ++ rest) = some (ps, rest) := by
  sorry

def Var_Connect.roundtrip (v : Var_Connect) (rest : List UInt8) :
  Var_Connect.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Connect.parser, Var_Connect.serialize]
  simp [Str.roundtrip]
  simp [UInt8.roundtrip]
  simp [Properties.roundtrip]

theorem Var_Connack.roundtrip (v : Var_Connack) (rest : List UInt8) :
  Var_Connack.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Connack.parser, Var_Connack.serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

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

theorem Var_Puback.roundtrip (v : Var_Puback) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Puback.parser, Var_Puback.serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Pubrec.roundtrip (v : Var_Pubrec) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Pubrel.roundtrip (v : Var_Pubrel) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Pubcomp.roundtrip (v : Var_Pubcomp) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Subscribe.roundtrip (v : Var_Subscribe) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Suback.roundtrip (v : Var_Suback) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Unsubscribe.roundtrip (v : Var_Unsubscribe) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Unsuback.roundtrip (v : Var_Unsuback) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Pingreq.roundtrip (v : Var_Pingreq) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]

theorem Var_Pingresp.roundtrip (v : Var_Pingresp) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]

theorem Var_Disconnect.roundtrip (v : Var_Disconnect) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

theorem Var_Auth.roundtrip (v : Var_Auth) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

theorem VarHeader.roundtrip_value
  {w : WhichPkt} {f : WhichPkt.flagType w} (v : VarHeader.getType w f) (rest : List UInt8) :
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


theorem VarHeader.roundtrip (h : FixedHeader) (v : VarHeader h) (rest : List UInt8) :
  (parser h).run (v.serialize h ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [VarHeader.roundtrip_value v]

end Mqtt
