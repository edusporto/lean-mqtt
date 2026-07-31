import LeanMqtt.Core.Codec
import LeanMqtt.Core.WithByteSize

namespace Mqtt
open Mqtt

/-!
# Constant Values

This module provides the generic `ConstVal` primitive for defining fields that
must exactly match a specific, statically known constant.
-/

/- ========================================================================= -/
/-! ## Constant Value Type (`ConstVal`) -/

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

@[simp]
def ConstVal.byteSize {α : Type} [GetByteSize α] {expected : α} (v : ConstVal α expected) : Nat :=
  GetByteSize.byteSize v.val

instance {α : Type} [GetByteSize α] {expected : α} : GetByteSize (ConstVal α expected) where
  byteSize := ConstVal.byteSize

instance {α : Type} {expected : α} [Codec α] [DecidableEq α] : Codec (ConstVal α expected) where
  parser := ConstVal.parser expected
  serialize := ConstVal.serialize

end Mqtt
