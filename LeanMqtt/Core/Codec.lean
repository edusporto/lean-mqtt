import LeanMqtt.Core.Parser.Basic

namespace Mqtt
open Mqtt

/--
  A typeclass for basic types that can be serialized and parsed without
  any external information.
-/
class Codec (α : Type) where
  parser : Parser α
  serialize : α → List UInt8

class LawfulCodec (α : Type) [Codec α] where
  roundtrip : ∀ (a : α) {rest : List UInt8},
    Codec.parser.run (Codec.serialize a ++ rest) = some (a, rest)
  reconstruct : ∀ {a : α} {input rest : List UInt8},
    Codec.parser.run input = some (a, rest) → input = Codec.serialize a ++ rest
