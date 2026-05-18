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

theorem Var_Connect.reconstruct
  (input : List UInt8) (v : Var_Connect) (rest : List UInt8) :
  Var_Connect.parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨p_name, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨p_ver, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨c_flags, m3, h5, h6⟩ := Parser.bind_run_success _ _ _ _ _ h4
  obtain ⟨props, m4, h7, h8⟩ := Parser.bind_run_success _ _ _ _ _ h6
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h8
  subst h_rest h_v
  rw [Str.reconstruct _ _ _ h1,
    UInt8.reconstruct _ _ _ h3,
    UInt8.reconstruct _ _ _ h5,
    Properties.reconstruct _ _ _ h7]
  simp only [List.append_assoc]

theorem Var_Connack.roundtrip (v : Var_Connack) (rest : List UInt8) :
  Var_Connack.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Connack.parser, Var_Connack.serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

theorem Var_Connack.reconstruct (input : List UInt8) (v : Var_Connack) (rest : List UInt8) :
  Var_Connack.parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨ack_flags, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨rcode, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨props, m3, h5, h6⟩ := Parser.bind_run_success _ _ _ _ _ h4
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h6
  subst h_rest h_v
  rw [UInt8.reconstruct _ _ _ h1,
    UInt8.reconstruct _ _ _ h3,
    Properties.reconstruct _ _ _ h5]
  simp only [List.append_assoc]

theorem Var_Publish.roundtrip {qos : QoSBits} (v : Var_Publish qos) (rest : List UInt8) :
  (Var_Publish.parser qos).run (v.serialize ++ rest) = some (v, rest) := by

  -- Unpack the subtype into its raw value and proof immediately.
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

theorem Var_Publish.reconstruct {qos : QoSBits} (input : List UInt8) (v : Var_Publish qos) (rest : List UInt8) :
  (Var_Publish.parser qos).run input = some (v, rest) → input = v.serialize ++ rest := by
  rcases qos with ⟨qos_val, h_qos⟩
  simp only [Var_Publish.parser, Var_Publish.serialize]
  intro h

  obtain ⟨topic, m1, h_topic, h_next1⟩ := Parser.bind_run_success _ _ _ _ _ h

  revert h_next1
  split
  · next h_qos_pos =>
    intro h_next1
    -- Extract UInt16.parser as a black box
    obtain ⟨pid, m2, h_pid, h_next2⟩ := Parser.bind_run_success _ _ _ _ _ h_next1

    -- Extract the `let y ← pure (cast ...)` statement
    obtain ⟨pid_cast, m2_mid, h_pure_cast, h_next3⟩ := Parser.bind_run_success _ _ _ _ _ h_next2
    obtain ⟨h_cast_eq, h_m2_eq⟩ := Parser.pure_run_success _ _ _ _ h_pure_cast
    subst h_m2_eq h_cast_eq

    -- Extract Properties.parser
    obtain ⟨props, m3, h_props, h_pure⟩ := Parser.bind_run_success _ _ _ _ _ h_next3

    -- Extract final pure return
    obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h_pure
    subst h_rest h_v

    -- Apply reconstruction helpers
    rw [Str.reconstruct _ _ _ h_topic, UInt16.reconstruct _ _ _ h_pid, Properties.reconstruct _ _ _ h_props]
    simp

  · next h_qos_zero =>
    intro h_next1

    -- Extract the `let y ← pure (cast ...)` statement
    obtain ⟨pid_cast, m2, h_pure_cast, h_next2⟩ := Parser.bind_run_success _ _ _ _ _ h_next1
    obtain ⟨h_cast_eq, h_m2_eq⟩ := Parser.pure_run_success _ _ _ _ h_pure_cast
    subst h_m2_eq h_cast_eq

    -- Extract Properties.parser
    obtain ⟨props, m3, h_props, h_pure⟩ := Parser.bind_run_success _ _ _ _ _ h_next2

    -- Extract final pure return
    obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h_pure
    subst h_rest h_v

    -- Apply reconstruction helpers
    rw [Str.reconstruct _ _ _ h_topic, Properties.reconstruct _ _ _ h_props]
    simp

theorem Var_Puback.roundtrip (v : Var_Puback) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Puback.parser, Var_Puback.serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Puback.reconstruct (input : List UInt8) (v : Var_Puback) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨pid, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨rcode, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨props, m3, h5, h6⟩ := Parser.bind_run_success _ _ _ _ _ h4
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h6
  subst h_rest h_v
  rw [UInt16.reconstruct _ _ _
    h1, UInt8.reconstruct _ _ _ h3,
    Properties.reconstruct _ _ _ h5]
  simp only [List.append_assoc]

theorem Var_Pubrec.roundtrip (v : Var_Pubrec) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Pubrec.reconstruct (input : List UInt8) (v : Var_Pubrec) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨pid, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨rcode, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨props, m3, h5, h6⟩ := Parser.bind_run_success _ _ _ _ _ h4
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h6
  subst h_rest h_v
  rw [UInt16.reconstruct _ _ _ h1,
    UInt8.reconstruct _ _ _ h3,
    Properties.reconstruct _ _ _ h5]
  simp only [List.append_assoc]

theorem Var_Pubrel.roundtrip (v : Var_Pubrel) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Pubrel.reconstruct (input : List UInt8) (v : Var_Pubrel) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨pid, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨rcode, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨props, m3, h5, h6⟩ := Parser.bind_run_success _ _ _ _ _ h4
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h6
  subst h_rest h_v
  rw [UInt16.reconstruct _ _ _ h1,
    UInt8.reconstruct _ _ _ h3,
    Properties.reconstruct _ _ _ h5]
  simp only [List.append_assoc]

theorem Var_Pubcomp.roundtrip (v : Var_Pubcomp) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Pubcomp.reconstruct (input : List UInt8) (v : Var_Pubcomp) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨pid, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨rcode, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨props, m3, h5, h6⟩ := Parser.bind_run_success _ _ _ _ _ h4
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h6
  subst h_rest h_v
  rw [UInt16.reconstruct _ _ _ h1,
    UInt8.reconstruct _ _ _ h3,
    Properties.reconstruct _ _ _ h5]
  simp only [List.append_assoc]

theorem Var_Subscribe.roundtrip (v : Var_Subscribe) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Subscribe.reconstruct (input : List UInt8) (v : Var_Subscribe) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨pid, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨props, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h4
  subst h_rest h_v
  rw [UInt16.reconstruct _ _ _ h1, Properties.reconstruct _ _ _ h3]
  simp only [List.append_assoc]

theorem Var_Suback.roundtrip (v : Var_Suback) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Suback.reconstruct (input : List UInt8) (v : Var_Suback) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨pid, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨props, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h4
  subst h_rest h_v
  rw [UInt16.reconstruct _ _ _ h1, Properties.reconstruct _ _ _ h3]
  simp only [List.append_assoc]

theorem Var_Unsubscribe.roundtrip (v : Var_Unsubscribe) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Unsubscribe.reconstruct (input : List UInt8) (v : Var_Unsubscribe) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨pid, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨props, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h4
  subst h_rest h_v
  rw [UInt16.reconstruct _ _ _ h1, Properties.reconstruct _ _ _ h3]
  simp only [List.append_assoc]

theorem Var_Unsuback.roundtrip (v : Var_Unsuback) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Unsuback.reconstruct (input : List UInt8) (v : Var_Unsuback) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨pid, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨props, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h4
  subst h_rest h_v
  rw [UInt16.reconstruct _ _ _ h1, Properties.reconstruct _ _ _ h3]
  simp only [List.append_assoc]

theorem Var_Pingreq.roundtrip (v : Var_Pingreq) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]

  theorem Var_Pingreq.reconstruct (input : List UInt8) (v : Var_Pingreq) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h
  subst h_rest h_v
  rfl

theorem Var_Pingresp.roundtrip (v : Var_Pingresp) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]

theorem Var_Pingresp.reconstruct (input : List UInt8) (v : Var_Pingresp) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h
  subst h_rest h_v
  rfl

theorem Var_Disconnect.roundtrip (v : Var_Disconnect) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

theorem Var_Disconnect.reconstruct (input : List UInt8) (v : Var_Disconnect) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨rcode, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨props, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h4
  subst h_rest h_v
  rw [UInt8.reconstruct _ _ _ h1, Properties.reconstruct _ _ _ h3]
  simp only [List.append_assoc]

theorem Var_Auth.roundtrip (v : Var_Auth) (rest : List UInt8) :
  parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

theorem Var_Auth.reconstruct (input : List UInt8) (v : Var_Auth) (rest : List UInt8) :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  obtain ⟨rcode, m1, h1, h2⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨props, m2, h3, h4⟩ := Parser.bind_run_success _ _ _ _ _ h2
  obtain ⟨h_v, h_rest⟩ := Parser.pure_run_success _ _ _ _ h4
  subst h_rest h_v
  rw [UInt8.reconstruct _ _ _ h1, Properties.reconstruct _ _ _ h3]
  simp only [List.append_assoc]

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

theorem VarHeader.reconstruct_value
  {k : PktKind} {f : PktFlags k} (input : List UInt8) (v : VarHeader.getType k f) (rest : List UInt8) :
  (VarHeader.parserValue k f).run input = some (v, rest) → input = VarHeader.serializeValue v ++ rest := by

  cases k <;> simp [parserValue, serializeValue]
  · exact Var_Connect.reconstruct input v rest
  · exact Var_Connack.reconstruct input v rest
  · exact Var_Publish.reconstruct input v rest
  · exact Var_Puback.reconstruct input v rest
  · exact Var_Pubrec.reconstruct input v rest
  · exact Var_Pubrel.reconstruct input v rest
  · exact Var_Pubcomp.reconstruct input v rest
  · exact Var_Subscribe.reconstruct input v rest
  · exact Var_Suback.reconstruct input v rest
  · exact Var_Unsubscribe.reconstruct input v rest
  · exact Var_Unsuback.reconstruct input v rest
  · exact Var_Pingreq.reconstruct input v rest
  · exact Var_Pingresp.reconstruct input v rest
  · exact Var_Disconnect.reconstruct input v rest
  · exact Var_Auth.reconstruct input v rest

theorem VarHeader.roundtrip (h : FixedHeader) (v : VarHeader h) (rest : List UInt8) :
  (parser h).run (v.serialize h ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [VarHeader.roundtrip_value v]

theorem VarHeader.reconstruct (h : FixedHeader) (input : List UInt8) (v : VarHeader h) (rest : List UInt8) :
  (parser h).run input = some (v, rest) → input = v.serialize h ++ rest := by
  simp [parser, serialize]
  exact VarHeader.reconstruct_value input v rest

end Mqtt
