import LeanMqtt.Core.Codec

namespace Mqtt
open Mqtt

/--
  `ConstVal` is a generic primitive for fields that must exactly match a provided constant.
  It ensures the underlying value is equal to `expected`.
-/
abbrev ConstVal (α : Type) (expected : α) : Type :=
  { val : α // val = expected }

def ConstVal.serialize {α : Type} [c : Codec α] {expected : α}
    (v : ConstVal α expected) : List UInt8 :=
  @Codec.serialize α c v.val

def ConstVal.parser {α : Type} [c : Codec α] [DecidableEq α] (expected : α) : Parser (ConstVal α expected) := do
  let val ← @Codec.parser α c
  if h : val = expected then
    return ⟨val, h⟩
  else
    failure

end Mqtt
