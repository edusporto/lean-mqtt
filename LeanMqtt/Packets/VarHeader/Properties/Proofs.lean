import LeanMqtt.Packets.VarHeader.Basic
import LeanMqtt.Packets.VarHeader.Property.Basic
import LeanMqtt.Packets.VarHeader.Property.Proofs
import LeanMqtt.Packets.VarHeader.Properties.Basic
import LeanMqtt.Packets.VarHeader.Variations
import LeanMqtt.Primitives.Proofs

open Mqtt

-- TODO: prove
-- theoremt parsePropsLoop_len (chunk : List UInt8) (l : List Property) :
--   parsePropsLoop chunk = some l → chunk.length = (l.foldl (fun acc p => acc + p.byteSize) 0) := by
--   -- simp [GetByteSize.byteSize]
--   sorry

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
