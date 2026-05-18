import LeanMqtt.Core.Parser.Basic

namespace Mqtt
open Mqtt

/--
  A typeclass for basic, context-free types that can be serialized
  and parsed without any external information.
-/
class Codec (α : Type) where
  parser : Parser α
  serialize : α → List UInt8
  roundtrip : ∀ (a : α) (rest : List UInt8),
    parser.run (serialize a ++ rest) = some (a, rest)
  reconstruct : ∀ (input : List UInt8) (a : α) (rest : List UInt8),
    parser.run input = some (a, rest) → input = serialize a ++ rest
