import LeanMqtt.Primitives.Proofs
import LeanMqtt.Packets.VarHeader.Variations
import LeanMqtt.Packets.VarHeader.Properties.Proofs

namespace Mqtt
open Mqtt

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

theorem Var_Publish.roundtrip {qos : QoSBits} (v : Var_Publish qos) (rest : List UInt8) :
  (Var_Publish.parser qos).run (v.serialize ++ rest) = some (v, rest) := by

  -- 1. Unpack the subtype into its raw value and proof immediately.
  -- This prevents "motive is not type correct" errors later when we substitute.
  rcases qos with ⟨qos_val, h_qos⟩

  simp [Var_Publish.parser, Var_Publish.serialize]
  simp [Str.roundtrip]

  split
  · next h_qos_pos =>
    -- Case: QoS > 0
    simp [UInt16.roundtrip]
    simp [Properties.roundtrip]
  · next h_qos_zero =>
    -- Case: QoS == 0
    simp [Properties.roundtrip]
    congr

    have h_zero : qos_val = 0 := by bv_decide

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
  {k : PktKind} {f : PktFlags k} (v : VarHeader.getType k f) (rest : List UInt8) :
  (VarHeader.parserValue k f).run (VarHeader.serializeValue v ++ rest) = some (v, rest) := by

  cases k <;> simp [parserValue, serializeValue]
  · exact Var_Connect.roundtrip v rest
  · exact Var_Connack.roundtrip v rest
  · exact Var_Publish.roundtrip v rest
  · exact Var_Puback.roundtrip v rest
  · exact Var_Pubrec.roundtrip v rest
  · exact Var_Pubrel.roundtrip v rest
  · exact Var_Pubcomp.roundtrip v rest
  · exact Var_Subscribe.roundtrip v rest
  · exact Var_Suback.roundtrip v rest
  · exact Var_Unsubscribe.roundtrip v rest
  · exact Var_Unsuback.roundtrip v rest
  · exact Var_Pingreq.roundtrip v rest
  · exact Var_Pingresp.roundtrip v rest
  · exact Var_Disconnect.roundtrip v rest
  · exact Var_Auth.roundtrip v rest

theorem VarHeader.roundtrip (h : FixedHeader) (v : VarHeader h) (rest : List UInt8) :
  (parser h).run (v.serialize h ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [VarHeader.roundtrip_value v]

end Mqtt
