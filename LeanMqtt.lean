import LeanMqtt.Packets.Basic
import LeanMqtt.Packets.Proofs
import LeanMqtt.Primitives.Basic
import LeanMqtt.Primitives.Proofs

-- TMP: things I need for the full project compilation
-- (currently empty)

/-!
# Lean MQTT

This project contains a verified parser for the MQTT v5.0 protocol, based on
the [official OASIS specification](https://mqtt.org/mqtt-specification/).

Verified, in this project, means that the implementation respects two key
properties: _roundtrip_ and _reconstruction_, equivalent to _completeness_ and
_soundness_ respectively. The former means that parsing a serialized value
will perfectly recover that value, and the latter means that if parsing a value
succeeded, then it must be exactly the result of that value's serialization.

The approach builds on composable primitives in `LeanMqtt.Primitives.Basic` to
represent packets in `LeanMqtt.Packets.Basic` and their corresponding proofs in
`LeanMqtt.Packets.Proofs`.

For more information, we refer to the accompanying paper, to be presented at
[SBLP 2026](https://cbsoft.sbc.org.br/2026/en/symposiums/sblp/call/).
-/
