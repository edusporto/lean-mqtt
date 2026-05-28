import LeanMqtt.Primitives.Proofs
import LeanMqtt.Primitives.OptType.Proofs
import LeanMqtt.Helpers.ParserTactics
import LeanMqtt.Packets.VarHeader.Variations
import LeanMqtt.Packets.VarHeader.Properties.Proofs

namespace Mqtt
open Mqtt

def Var_Connect.roundtrip (v : Var_Connect) {rest : List UInt8} :
    Var_Connect.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Connect.parser, Var_Connect.serialize]
  simp [Str.roundtrip]
  simp [UInt8.roundtrip]
  simp [Properties.roundtrip]

theorem Var_Connect.reconstruct
    {v : Var_Connect} {input rest : List UInt8} :
    Var_Connect.parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → p_nameVal rest1 h_p_nameVal
  step_parser h → p_verVal rest2 h_p_verVal
  step_parser h → c_flagsVal rest3 h_c_flagsVal
  step_parser h → propsVal rest4 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [Str.reconstruct h_p_nameVal,
    UInt8.reconstruct h_p_verVal,
    UInt8.reconstruct h_c_flagsVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Connack.roundtrip (v : Var_Connack) {rest : List UInt8} :
    Var_Connack.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Connack.parser, Var_Connack.serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

theorem Var_Connack.reconstruct {v : Var_Connack} {input rest : List UInt8} :
    Var_Connack.parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → ack_flagsVal rest1 h_ack_flagsVal
  step_parser h → rcodeVal rest2 h_rcodeVal
  step_parser h → propsVal rest3 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt8.reconstruct h_ack_flagsVal,
    UInt8.reconstruct h_rcodeVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Publish.roundtrip {qos : QoSBits} (v : Var_Publish qos) {rest : List UInt8} :
    (Var_Publish.parser qos).run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Publish.parser, Var_Publish.serialize]
  simp [Str.roundtrip, OptType.roundtrip, Properties.roundtrip]

theorem Var_Publish.reconstruct {qos : QoSBits} {v : Var_Publish qos} {input rest : List UInt8} :
    (Var_Publish.parser qos).run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [Var_Publish.parser, Var_Publish.serialize]
  intro h

  step_parser h → topicVal rest1 h_topicVal
  step_parser h → pidVal rest2 h_pidVal
  step_parser h → propsVal rest3 h_propsVal
  finish_parser h → h_v
  subst h_v

  rw [Str.reconstruct h_topicVal,
      OptType.reconstruct (qos.val > 0) h_pidVal,
      Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Puback.roundtrip (v : Var_Puback) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Puback.parser, Var_Puback.serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Puback.reconstruct {v : Var_Puback} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → pidVal rest1 h_pidVal
  step_parser h → rcodeVal rest2 h_rcodeVal
  step_parser h → propsVal rest3 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt16.reconstruct h_pidVal,
      UInt8.reconstruct h_rcodeVal,
      Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Pubrec.roundtrip (v : Var_Pubrec) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Pubrec.reconstruct {v : Var_Pubrec} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → pidVal rest1 h_pidVal
  step_parser h → rcodeVal rest2 h_rcodeVal
  step_parser h → propsVal rest3 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt16.reconstruct h_pidVal,
    UInt8.reconstruct h_rcodeVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Pubrel.roundtrip (v : Var_Pubrel) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Pubrel.reconstruct {v : Var_Pubrel} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → pidVal rest1 h_pidVal
  step_parser h → rcodeVal rest2 h_rcodeVal
  step_parser h → propsVal rest3 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt16.reconstruct h_pidVal,
    UInt8.reconstruct h_rcodeVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Pubcomp.roundtrip (v : Var_Pubcomp) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, UInt8.roundtrip, Properties.roundtrip]

theorem Var_Pubcomp.reconstruct {v : Var_Pubcomp} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → pidVal rest1 h_pidVal
  step_parser h → rcodeVal rest2 h_rcodeVal
  step_parser h → propsVal rest3 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt16.reconstruct h_pidVal,
    UInt8.reconstruct h_rcodeVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Subscribe.roundtrip (v : Var_Subscribe) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Subscribe.reconstruct {v : Var_Subscribe} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → pidVal rest1 h_pidVal
  step_parser h → propsVal rest2 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt16.reconstruct h_pidVal, Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Suback.roundtrip (v : Var_Suback) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Suback.reconstruct {v : Var_Suback} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → pidVal rest1 h_pidVal
  step_parser h → propsVal rest2 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt16.reconstruct h_pidVal, Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Unsubscribe.roundtrip (v : Var_Unsubscribe) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Unsubscribe.reconstruct {v : Var_Unsubscribe} {input rest : List UInt8} :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → pidVal rest1 h_pidVal
  step_parser h → propsVal rest2 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt16.reconstruct h_pidVal, Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Unsuback.roundtrip (v : Var_Unsuback) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, Properties.roundtrip]

theorem Var_Unsuback.reconstruct {v : Var_Unsuback} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → pidVal rest1 h_pidVal
  step_parser h → propsVal rest2 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt16.reconstruct h_pidVal, Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Pingreq.roundtrip (v : Var_Pingreq) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]

theorem Var_Pingreq.reconstruct {v : Var_Pingreq} {input rest : List UInt8} :
  parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  finish_parser h → h_v
  subst h_v
  rfl

theorem Var_Pingresp.roundtrip (v : Var_Pingresp) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]

theorem Var_Pingresp.reconstruct {v : Var_Pingresp} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  finish_parser h → h_v
  subst h_v
  rfl

theorem Var_Disconnect.roundtrip (v : Var_Disconnect) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

theorem Var_Disconnect.reconstruct {v : Var_Disconnect} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → rcodeVal rest1 h_rcodeVal
  step_parser h → propsVal rest2 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt8.reconstruct h_rcodeVal, Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Auth.roundtrip (v : Var_Auth) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt8.roundtrip, Properties.roundtrip]

theorem Var_Auth.reconstruct {v : Var_Auth} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → rcodeVal rest1 h_rcodeVal
  step_parser h → propsVal rest2 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [UInt8.reconstruct h_rcodeVal, Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem VarHeader.roundtrip_value
    {k : PktKind} {f : PktFlags k} (v : VarHeader.getType k f) (rest : List UInt8) :
    (VarHeader.parserValue k f).run (VarHeader.serializeValue v ++ rest) = some (v, rest) := by

  cases k <;> simp [parserValue, serializeValue]
  · exact Var_Connect.roundtrip v
  · exact Var_Connack.roundtrip v
  · exact Var_Publish.roundtrip v
  · exact Var_Puback.roundtrip v
  · exact Var_Pubrec.roundtrip v
  · exact Var_Pubrel.roundtrip v
  · exact Var_Pubcomp.roundtrip v
  · exact Var_Subscribe.roundtrip v
  · exact Var_Suback.roundtrip v
  · exact Var_Unsubscribe.roundtrip v
  · exact Var_Unsuback.roundtrip v
  · exact Var_Pingreq.roundtrip v
  · exact Var_Pingresp.roundtrip v
  · exact Var_Disconnect.roundtrip v
  · exact Var_Auth.roundtrip v

theorem VarHeader.reconstruct_value
    {k : PktKind} {f : PktFlags k} {v : VarHeader.getType k f} {input rest : List UInt8} :
    (VarHeader.parserValue k f).run input = some (v, rest) →
    input = VarHeader.serializeValue v ++ rest := by

  cases k <;> simp [parserValue, serializeValue]
  · exact Var_Connect.reconstruct
  · exact Var_Connack.reconstruct
  · exact Var_Publish.reconstruct
  · exact Var_Puback.reconstruct
  · exact Var_Pubrec.reconstruct
  · exact Var_Pubrel.reconstruct
  · exact Var_Pubcomp.reconstruct
  · exact Var_Subscribe.reconstruct
  · exact Var_Suback.reconstruct
  · exact Var_Unsubscribe.reconstruct
  · exact Var_Unsuback.reconstruct
  · exact Var_Pingreq.reconstruct
  · exact Var_Pingresp.reconstruct
  · exact Var_Disconnect.reconstruct
  · exact Var_Auth.reconstruct

theorem VarHeader.roundtrip {fh : FixedHeader} (v : VarHeader fh) {rest : List UInt8} :
    (VarHeader.parser fh).run (v.serialize fh ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [VarHeader.roundtrip_value v]

theorem VarHeader.reconstruct
    {fh : FixedHeader} {v : VarHeader fh} {input rest : List UInt8} :
    (VarHeader.parser fh).run input = some (v, rest) → input = v.serialize fh ++ rest := by
  simp [parser, serialize]
  exact VarHeader.reconstruct_value

end Mqtt
