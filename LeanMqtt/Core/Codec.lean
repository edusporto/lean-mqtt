import LeanMqtt.Core.Parser.Basic

namespace Mqtt
open Mqtt

/-!
# Codec

This module containts type classes for _codecs_, which are types that can be
serialized and parsed without an external context. For example, `String`s
require the external context of their size to be parsed, while `Str`s don't.
-/

/--
  A typeclass for basic types that can be serialized and parsed without
  an external context.
-/
class Codec (α : Type) where
  parser : Parser α
  serialize : α → List UInt8

/--
  The main theorems we prove for the verified parser: _roundtrip_ and
  _reconstruction_.
-/
class LawfulCodec (α : Type) [Codec α] where
  roundtrip : ∀ (a : α) {rest : List UInt8},
    Codec.parser.run (Codec.serialize a ++ rest) = some (a, rest)
  reconstruct : ∀ {a : α} {input rest : List UInt8},
    Codec.parser.run input = some (a, rest) → input = Codec.serialize a ++ rest
