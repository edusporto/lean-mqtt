import LeanMqtt.Core.Codec

namespace Mqtt
open Mqtt

/--
  `PredType` is a generic primitive for fields that are only correct when a
  given predicate is true.
-/
abbrev PredType {α : Type} (p : α → Prop) : Type :=
  { val : α // p val }

def PredType.serialize {α : Type} [c : Codec α] {p : α → Prop} (v : PredType p) : List UInt8 :=
  @Codec.serialize α c v.val

def PredType.parser {α : Type} [c : Codec α] (p : α → Prop) [DecidablePred p] : Parser (PredType p) := do
  let val ← @Codec.parser α c
  if h : p val then
    return ⟨val, h⟩
  else
    failure

end Mqtt
