import LeanMqtt.Primitives.UInt.Basic
import LeanMqtt.Primitives.VarInt.Basic
import LeanMqtt.Primitives.Str.Basic
import LeanMqtt.Primitives.SizedList.Basic
import LeanMqtt.Primitives.OptType.Basic
import LeanMqtt.Primitives.ConstVal.Basic
import LeanMqtt.Primitives.PredType.Basic

/-!
# Primitives

This module contains the basic primitives used to build a parser for the MQTT protocol.

We classify these primitives into two types: *protocol* primitives and *combinator* primitives.
They are all includes as a subdirectory of `LeanMqtt.Primitives`: `Basic` files include the main
types and serialization/parsing functions, and `Proofs` files include their proofs of
roundtrip/reconstruction as well as supporting lemmas.

## Protocol primitives

These include primitive definitions directly specified by the protocol. In MQTT, they include:
- Fixed-size unsigned integers (`LeanMqtt.Primitives.UInt.Basic`)
- Variable Byte Integers (`LeanMqtt.Primitives.VarInt.Basic`)
- Strings and Binary Data (`LeanMqtt.Primitives.Str.Basic`)

## Combinator primitives

These are higher-order parser combinators that receive a parseable type (implements the
`Codec` class) and change the parsing behavior. In the current phase of the project, they
include:
- Length-prefixed lists (`LeanMqtt.Primitives.SizedList.Basic`)
- Conditionally optional values (`LeanMqtt.Primitives.OptType.Basic`)
- Constant values (`LeanMqtt.Primitives.ConstVal.Basic`)
- Values satisfying a list of predicates (`LeanMqtt.Primitives.PredType.Basic`)
-/
