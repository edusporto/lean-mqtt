import LeanMqtt.Primitives.UInt.Proofs
import LeanMqtt.Primitives.Str.Proofs
import LeanMqtt.Primitives.OptType.Proofs
import LeanMqtt.Primitives.ConstVal.Proofs
import LeanMqtt.Primitives.PredType.Proofs
import LeanMqtt.Helpers.ParserTactics
import LeanMqtt.Packets.VarHeader.Variations
import LeanMqtt.Packets.VarHeader.Properties.Proofs
import LeanMqtt.Packets.ReasonCode.Proofs

namespace Mqtt
open Mqtt

/- ========================================================================= -/
/-! ## CONNECT Variable Header (`Var_Connect`) -/

theorem Var_Connect.roundtrip (v : Var_Connect) {rest : List UInt8} :
    Var_Connect.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Connect.parser, Var_Connect.serialize]
  simp [ConstVal.roundtrip]
  simp [PredType.roundtrip]
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
  rw [ConstVal.reconstruct _ h_p_nameVal,
    ConstVal.reconstruct _ h_p_verVal,
    PredType.reconstruct ConnectFlagsPred h_c_flagsVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Connect.serialize_len (v : Var_Connect) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Connect.serialize, GetByteSize.byteSize, Var_Connect.byteSize]
  simp only [List.length_append]
  simp only [ConstVal.serialize_len v.protocol_name,
    ConstVal.serialize_len v.protocol_version,
    PredType.serialize_len v.connect_flags,
    Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## CONNACK Variable Header (`Var_Connack`) -/

theorem Var_Connack.roundtrip (v : Var_Connack) {rest : List UInt8} :
    Var_Connack.parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Connack.parser, Var_Connack.serialize]
  simp [ReasonCode.roundtrip, Properties.roundtrip, PredType.roundtrip]

theorem Var_Connack.reconstruct {v : Var_Connack} {input rest : List UInt8} :
    Var_Connack.parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → ack_flagsVal rest1 h_ack_flagsVal
  step_parser h → rcodeVal rest2 h_rcodeVal
  step_parser h → propsVal rest3 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [PredType.reconstruct ConnackFlagsProp h_ack_flagsVal,
    ReasonCode.reconstruct h_rcodeVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Connack.serialize_len (v : Var_Connack) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Connack.serialize, GetByteSize.byteSize, Var_Connack.byteSize]
  simp only [List.length_append]
  simp only [PredType.serialize_len v.ack_flags,
    ReasonCode.serialize_len v.reason_code,
    Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## PUBLISH Variable Header (`Var_Publish`) -/

theorem Var_Publish.roundtrip {qos : QoSBits} (v : Var_Publish qos) {rest : List UInt8} :
    (Var_Publish.parser qos).run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Publish.parser, Var_Publish.serialize]
  simp [PredType.roundtrip, OptType.roundtrip, Properties.roundtrip]

theorem Var_Publish.reconstruct {qos : QoSBits} {v : Var_Publish qos} {input rest : List UInt8} :
    (Var_Publish.parser qos).run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [Var_Publish.parser, Var_Publish.serialize]
  intro h

  step_parser h → topicVal rest1 h_topicVal
  step_parser h → pidVal rest2 h_pidVal
  step_parser h → propsVal rest3 h_propsVal
  finish_parser h → h_v
  subst h_v

  rw [PredType.reconstruct TopicNameProp h_topicVal,
      OptType.reconstruct (qos.val > 0) h_pidVal,
      Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Publish.serialize_len {qos : QoSBits} (v : Var_Publish qos) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Publish.serialize, GetByteSize.byteSize, Var_Publish.byteSize]
  simp only [List.length_append]
  simp only [PredType.serialize_len v.topic_name,
    OptType.serialize_len v.packet_id,
    Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## PUBACK Variable Header (`Var_Puback`) -/

theorem Var_Puback.roundtrip (v : Var_Puback) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [Var_Puback.parser, Var_Puback.serialize]
  simp [UInt16.roundtrip, ReasonCode.roundtrip, Properties.roundtrip]

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
      ReasonCode.reconstruct h_rcodeVal,
      Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Puback.serialize_len (v : Var_Puback) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Puback.serialize, GetByteSize.byteSize, Var_Puback.byteSize]
  simp only [List.length_append]
  simp only [ReasonCode.serialize_len v.reason_code, Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## PUBREC Variable Header (`Var_Pubrec`) -/

theorem Var_Pubrec.roundtrip (v : Var_Pubrec) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, ReasonCode.roundtrip, Properties.roundtrip]

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
    ReasonCode.reconstruct h_rcodeVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Pubrec.serialize_len (v : Var_Pubrec) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Pubrec.serialize, GetByteSize.byteSize, Var_Pubrec.byteSize]
  simp only [List.length_append]
  simp only [ReasonCode.serialize_len v.reason_code, Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## PUBREL Variable Header (`Var_Pubrel`) -/

theorem Var_Pubrel.roundtrip (v : Var_Pubrel) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, ReasonCode.roundtrip, Properties.roundtrip]

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
    ReasonCode.reconstruct h_rcodeVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Pubrel.serialize_len (v : Var_Pubrel) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Pubrel.serialize, GetByteSize.byteSize, Var_Pubrel.byteSize]
  simp only [List.length_append]
  simp only [ReasonCode.serialize_len v.reason_code, Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## PUBCOMP Variable Header (`Var_Pubcomp`) -/

theorem Var_Pubcomp.roundtrip (v : Var_Pubcomp) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [UInt16.roundtrip, ReasonCode.roundtrip, Properties.roundtrip]

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
    ReasonCode.reconstruct h_rcodeVal,
    Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Pubcomp.serialize_len (v : Var_Pubcomp) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Pubcomp.serialize, GetByteSize.byteSize, Var_Pubcomp.byteSize]
  simp only [List.length_append]
  simp only [ReasonCode.serialize_len v.reason_code, Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## SUBSCRIBE Variable Header (`Var_Subscribe`) -/

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

theorem Var_Subscribe.serialize_len (v : Var_Subscribe) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Subscribe.serialize, GetByteSize.byteSize, Var_Subscribe.byteSize]
  simp only [List.length_append]
  simp only [Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## SUBACK Variable Header (`Var_Suback`) -/

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

theorem Var_Suback.serialize_len (v : Var_Suback) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Suback.serialize, GetByteSize.byteSize, Var_Suback.byteSize]
  simp only [List.length_append]
  simp only [Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## UNSUBSCRIBE Variable Header (`Var_Unsubscribe`) -/

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

theorem Var_Unsubscribe.serialize_len (v : Var_Unsubscribe) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Unsubscribe.serialize, GetByteSize.byteSize, Var_Unsubscribe.byteSize]
  simp only [List.length_append]
  simp only [Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## UNSUBACK Variable Header (`Var_Unsuback`) -/

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

theorem Var_Unsuback.serialize_len (v : Var_Unsuback) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Unsuback.serialize, GetByteSize.byteSize, Var_Unsuback.byteSize]
  simp only [List.length_append]
  simp only [Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## PINGREQ Variable Header (`Var_Pingreq`) -/

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

theorem Var_Pingreq.serialize_len (v : Var_Pingreq) :
    v.serialize.length = GetByteSize.byteSize v := by
  rfl

/- ========================================================================= -/
/-! ## PINGRESP Variable Header (`Var_Pingresp`) -/

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

theorem Var_Pingresp.serialize_len (v : Var_Pingresp) :
    v.serialize.length = GetByteSize.byteSize v := by
  rfl

/- ========================================================================= -/
/-! ## DISCONNECT Variable Header (`Var_Disconnect`) -/

theorem Var_Disconnect.roundtrip (v : Var_Disconnect) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [ReasonCode.roundtrip, Properties.roundtrip]

theorem Var_Disconnect.reconstruct {v : Var_Disconnect} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → rcodeVal rest1 h_rcodeVal
  step_parser h → propsVal rest2 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [ReasonCode.reconstruct h_rcodeVal, Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Disconnect.serialize_len (v : Var_Disconnect) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Disconnect.serialize, GetByteSize.byteSize, Var_Disconnect.byteSize]
  simp only [List.length_append]
  simp only [ReasonCode.serialize_len v.reason_code, Properties.serialize_len v.props]
  rfl


/- ========================================================================= -/
/-! ## AUTH Variable Header (`Var_Auth`) -/

theorem Var_Auth.roundtrip (v : Var_Auth) {rest : List UInt8} :
    parser.run (v.serialize ++ rest) = some (v, rest) := by
  simp [parser, serialize]
  simp [ReasonCode.roundtrip, Properties.roundtrip]

theorem Var_Auth.reconstruct {v : Var_Auth} {input rest : List UInt8} :
    parser.run input = some (v, rest) → input = v.serialize ++ rest := by
  simp only [parser, serialize]
  intro h
  step_parser h → rcodeVal rest1 h_rcodeVal
  step_parser h → propsVal rest2 h_propsVal
  finish_parser h → h_v
  subst h_v
  rw [ReasonCode.reconstruct h_rcodeVal, Properties.reconstruct h_propsVal]
  simp only [List.append_assoc]

theorem Var_Auth.serialize_len (v : Var_Auth) :
    v.serialize.length = GetByteSize.byteSize v := by
  simp only [Var_Auth.serialize, GetByteSize.byteSize, Var_Auth.byteSize]
  simp only [List.length_append]
  simp only [ReasonCode.serialize_len v.reason_code, Properties.serialize_len v.props]
  rfl

/- ========================================================================= -/
/-! ## Variable Header (`VarHeader`) -/

theorem VarHeader.serializeValue_len {k : PktKind} {f : PktFlags k} (v : VarHeader.getType k f) :
    (VarHeader.serializeValue v).length = VarHeader.byteSizeValue v := by
  cases k <;> simp [VarHeader.serializeValue, VarHeader.byteSizeValue]
  · exact Var_Connect.serialize_len v
  · exact Var_Connack.serialize_len v
  · exact Var_Publish.serialize_len v
  · exact Var_Puback.serialize_len v
  · exact Var_Pubrec.serialize_len v
  · exact Var_Pubrel.serialize_len v
  · exact Var_Pubcomp.serialize_len v
  · exact Var_Subscribe.serialize_len v
  · exact Var_Suback.serialize_len v
  · exact Var_Unsubscribe.serialize_len v
  · exact Var_Unsuback.serialize_len v
  · rfl
  · rfl
  · exact Var_Disconnect.serialize_len v
  · exact Var_Auth.serialize_len v

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

theorem VarHeader.serialize_len {fh : FixedHeader} (v : VarHeader fh) :
    (VarHeader.serialize fh v).length = GetByteSize.byteSize v := by
  exact VarHeader.serializeValue_len v

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
