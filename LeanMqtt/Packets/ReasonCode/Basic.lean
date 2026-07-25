import LeanMqtt.Core.Codec
import LeanMqtt.Primitives.UInt.Basic
import LeanMqtt.Packets.FixedHeader.Basic
import LeanMqtt.Helpers.EnumUtils

namespace Mqtt

enum_with_codec GlobalReasonCode : UInt8 {
  success => 0x00
  granted_qos_1 => 0x01
  granted_qos_2 => 0x02
  disconnect_with_will_message => 0x04
  no_matching_subscribers => 0x10
  no_subscription_existed => 0x11
  continue_authentication => 0x18
  re_authenticate => 0x19
  unspecified_error => 0x80
  malformed_packet => 0x81
  protocol_error => 0x82
  implementation_specific_error => 0x83
  unsupported_protocol_version => 0x84
  client_identifier_not_valid => 0x85
  bad_user_name_or_password => 0x86
  not_authorized => 0x87
  server_unavailable => 0x88
  server_busy => 0x89
  banned => 0x8A
  server_shutting_down => 0x8B
  bad_authentication_method => 0x8C
  keep_alive_timeout => 0x8D
  session_taken_over => 0x8E
  topic_filter_invalid => 0x8F
  topic_name_invalid => 0x90
  packet_identifier_in_use => 0x91
  packet_identifier_not_found => 0x92
  receive_maximum_exceeded => 0x93
  topic_alias_invalid => 0x94
  packet_too_large => 0x95
  message_rate_too_high => 0x96
  quota_exceeded => 0x97
  administrative_action => 0x98
  payload_format_invalid => 0x99
  retain_not_supported => 0x9A
  qos_not_supported => 0x9B
  use_another_server => 0x9C
  server_moved => 0x9D
  shared_subscriptions_not_supported => 0x9E
  connection_rate_exceeded => 0x9F
  maximum_connect_time => 0xA0
  subscription_identifiers_not_supported => 0xA1
  wildcard_subscriptions_not_supported => 0xA2
}

def GlobalReasonCode.serialize (rc : GlobalReasonCode) : List UInt8 :=
  [rc.encode]

def GlobalReasonCode.parser : Parser GlobalReasonCode := do
  let b ← UInt8.parser
  let rc ← GlobalReasonCode.decode? b
  return rc

valid_variants isValidReasonCode : PktKind → GlobalReasonCode {
  connack => [
    success, unspecified_error, malformed_packet, protocol_error,
    implementation_specific_error, unsupported_protocol_version,
    client_identifier_not_valid, bad_user_name_or_password,
    not_authorized, server_unavailable, server_busy, banned,
    bad_authentication_method, topic_name_invalid, packet_too_large,
    quota_exceeded, payload_format_invalid, retain_not_supported,
    qos_not_supported, use_another_server, server_moved,
    connection_rate_exceeded
  ]
  puback => [
    success, no_matching_subscribers, unspecified_error,
    implementation_specific_error, not_authorized, topic_name_invalid,
    packet_identifier_in_use, quota_exceeded, payload_format_invalid
  ]
  pubrec => [
    success, no_matching_subscribers, unspecified_error,
    implementation_specific_error, not_authorized, topic_name_invalid,
    packet_identifier_in_use, quota_exceeded, payload_format_invalid
  ]
  pubrel => [
    success, unspecified_error, implementation_specific_error,
    packet_identifier_not_found
  ]
  pubcomp => [
    success, unspecified_error, implementation_specific_error,
    packet_identifier_not_found
  ]
  suback => [
    success, granted_qos_1, granted_qos_2, unspecified_error,
    implementation_specific_error, not_authorized, topic_filter_invalid,
    packet_identifier_in_use, quota_exceeded, shared_subscriptions_not_supported,
    subscription_identifiers_not_supported, wildcard_subscriptions_not_supported
  ]
  unsuback => [
    success, no_subscription_existed, unspecified_error,
    implementation_specific_error, not_authorized, topic_filter_invalid,
    packet_identifier_in_use
  ]
  disconnect => [
    success, disconnect_with_will_message, unspecified_error,
    malformed_packet, protocol_error, implementation_specific_error,
    not_authorized, server_busy, server_shutting_down, keep_alive_timeout,
    session_taken_over, topic_filter_invalid, topic_name_invalid,
    receive_maximum_exceeded, topic_alias_invalid, packet_too_large,
    message_rate_too_high, quota_exceeded, administrative_action,
    payload_format_invalid, retain_not_supported, qos_not_supported,
    use_another_server, server_moved, shared_subscriptions_not_supported,
    connection_rate_exceeded, maximum_connect_time,
    subscription_identifiers_not_supported, wildcard_subscriptions_not_supported
  ]
  auth => [
    success, continue_authentication, re_authenticate
  ]
}

def ReasonCode (p : PktKind) := { rc : GlobalReasonCode // isValidReasonCode p rc }

def ReasonCode.serialize {p : PktKind} (prc : ReasonCode p) : List UInt8 :=
  prc.val.serialize

def ReasonCode.parser (p : PktKind) : Parser (ReasonCode p) := do
  let rc ← GlobalReasonCode.parser
  if h : isValidReasonCode p rc = true then
    pure ⟨rc, h⟩
  else
    failure

end Mqtt
