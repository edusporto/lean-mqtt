import LeanMqtt.Core.Codec
import LeanMqtt.Primitives.UInt.Basic

namespace Mqtt

inductive ReasonCode where
  | success -- 0x00
  | granted_qos_1 -- 0x01
  | granted_qos_2 -- 0x02
  | disconnect_with_will_message -- 0x04
  | no_matching_subscribers -- 0x10
  | no_subscription_existed -- 0x11
  | continue_authentication -- 0x18
  | re_authenticate -- 0x19
  | unspecified_error -- 0x80
  | malformed_packet -- 0x81
  | protocol_error -- 0x82
  | implementation_specific_error -- 0x83
  | unsupported_protocol_version -- 0x84
  | client_identifier_not_valid -- 0x85
  | bad_user_name_or_password -- 0x86
  | not_authorized -- 0x87
  | server_unavailable -- 0x88
  | server_busy -- 0x89
  | banned -- 0x8A
  | server_shutting_down -- 0x8B
  | bad_authentication_method -- 0x8C
  | keep_alive_timeout -- 0x8D
  | session_taken_over -- 0x8E
  | topic_filter_invalid -- 0x8F
  | topic_name_invalid -- 0x90
  | packet_identifier_in_use -- 0x91
  | packet_identifier_not_found -- 0x92
  | receive_maximum_exceeded -- 0x93
  | topic_alias_invalid -- 0x94
  | packet_too_large -- 0x95
  | message_rate_too_high -- 0x96
  | quota_exceeded -- 0x97
  | administrative_action -- 0x98
  | payload_format_invalid -- 0x99
  | retain_not_supported -- 0x9A
  | qos_not_supported -- 0x9B
  | use_another_server -- 0x9C
  | server_moved -- 0x9D
  | shared_subscriptions_not_supported -- 0x9E
  | connection_rate_exceeded -- 0x9F
  | maximum_connect_time -- 0xA0
  | subscription_identifiers_not_supported -- 0xA1
  | wildcard_subscriptions_not_supported -- 0xA2
deriving Repr, BEq, Inhabited

def ReasonCode.encode : ReasonCode → UInt8
  | .success => 0x00
  | .granted_qos_1 => 0x01
  | .granted_qos_2 => 0x02
  | .disconnect_with_will_message => 0x04
  | .no_matching_subscribers => 0x10
  | .no_subscription_existed => 0x11
  | .continue_authentication => 0x18
  | .re_authenticate => 0x19
  | .unspecified_error => 0x80
  | .malformed_packet => 0x81
  | .protocol_error => 0x82
  | .implementation_specific_error => 0x83
  | .unsupported_protocol_version => 0x84
  | .client_identifier_not_valid => 0x85
  | .bad_user_name_or_password => 0x86
  | .not_authorized => 0x87
  | .server_unavailable => 0x88
  | .server_busy => 0x89
  | .banned => 0x8A
  | .server_shutting_down => 0x8B
  | .bad_authentication_method => 0x8C
  | .keep_alive_timeout => 0x8D
  | .session_taken_over => 0x8E
  | .topic_filter_invalid => 0x8F
  | .topic_name_invalid => 0x90
  | .packet_identifier_in_use => 0x91
  | .packet_identifier_not_found => 0x92
  | .receive_maximum_exceeded => 0x93
  | .topic_alias_invalid => 0x94
  | .packet_too_large => 0x95
  | .message_rate_too_high => 0x96
  | .quota_exceeded => 0x97
  | .administrative_action => 0x98
  | .payload_format_invalid => 0x99
  | .retain_not_supported => 0x9A
  | .qos_not_supported => 0x9B
  | .use_another_server => 0x9C
  | .server_moved => 0x9D
  | .shared_subscriptions_not_supported => 0x9E
  | .connection_rate_exceeded => 0x9F
  | .maximum_connect_time => 0xA0
  | .subscription_identifiers_not_supported => 0xA1
  | .wildcard_subscriptions_not_supported => 0xA2

def ReasonCode.decode? : UInt8 → Option ReasonCode
  | 0x00 => some .success
  | 0x01 => some .granted_qos_1
  | 0x02 => some .granted_qos_2
  | 0x04 => some .disconnect_with_will_message
  | 0x10 => some .no_matching_subscribers
  | 0x11 => some .no_subscription_existed
  | 0x18 => some .continue_authentication
  | 0x19 => some .re_authenticate
  | 0x80 => some .unspecified_error
  | 0x81 => some .malformed_packet
  | 0x82 => some .protocol_error
  | 0x83 => some .implementation_specific_error
  | 0x84 => some .unsupported_protocol_version
  | 0x85 => some .client_identifier_not_valid
  | 0x86 => some .bad_user_name_or_password
  | 0x87 => some .not_authorized
  | 0x88 => some .server_unavailable
  | 0x89 => some .server_busy
  | 0x8A => some .banned
  | 0x8B => some .server_shutting_down
  | 0x8C => some .bad_authentication_method
  | 0x8D => some .keep_alive_timeout
  | 0x8E => some .session_taken_over
  | 0x8F => some .topic_filter_invalid
  | 0x90 => some .topic_name_invalid
  | 0x91 => some .packet_identifier_in_use
  | 0x92 => some .packet_identifier_not_found
  | 0x93 => some .receive_maximum_exceeded
  | 0x94 => some .topic_alias_invalid
  | 0x95 => some .packet_too_large
  | 0x96 => some .message_rate_too_high
  | 0x97 => some .quota_exceeded
  | 0x98 => some .administrative_action
  | 0x99 => some .payload_format_invalid
  | 0x9A => some .retain_not_supported
  | 0x9B => some .qos_not_supported
  | 0x9C => some .use_another_server
  | 0x9D => some .server_moved
  | 0x9E => some .shared_subscriptions_not_supported
  | 0x9F => some .connection_rate_exceeded
  | 0xA0 => some .maximum_connect_time
  | 0xA1 => some .subscription_identifiers_not_supported
  | 0xA2 => some .wildcard_subscriptions_not_supported
  | _ => none

def ReasonCode.serialize (rc : ReasonCode) : List UInt8 :=
  [rc.encode]

def ReasonCode.parser : Parser ReasonCode := do
  let b ← UInt8.parser
  let rc ← ReasonCode.decode? b
  return rc

end Mqtt
