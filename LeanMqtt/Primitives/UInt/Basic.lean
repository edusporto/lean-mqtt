import LeanMqtt.Core.Parser.Basic
import LeanMqtt.Core.WithByteSize
import LeanMqtt.Core.Codec

namespace Mqtt

/-!
# Unsigned Integers

This module defines parsing and serialization instances for Lean's standard
unsigned integer types (`UInt8`, `UInt16`, `UInt32`), specifically following
MQTT's big-endian network byte order format.
-/

/- ========================================================================= -/
/-! ## 8-bit Unsigned Integer (`UInt8`) -/

def UInt8.serialize (b : UInt8) : List UInt8 :=
  [b]

def UInt8.parser : Parser UInt8 := do
  match (← get) with
  | [] => none
  | b :: rest =>
    set rest
    some b

instance : Codec UInt8 where
  parser := UInt8.parser
  serialize := UInt8.serialize

@[simp] def UInt8.byteSize (_ : UInt8) : Nat := 1
instance : GetByteSize UInt8 where byteSize := UInt8.byteSize

/- ========================================================================= -/
/-! ## 16-bit Unsigned Integer (`UInt16`) -/

def UInt16.serialize (n : UInt16) : List UInt8 :=
  let b1 := (n >>> 8).toUInt8
  let b2 := n.toUInt8
  [b1, b2]

def UInt16.parser : Parser UInt16 := do
  let b1 ← UInt8.parser
  let b2 ← UInt8.parser
  return (b1.toUInt16 <<< 8) ||| b2.toUInt16

instance : Codec UInt16 where
  parser := UInt16.parser
  serialize := UInt16.serialize

@[simp] def UInt16.byteSize (_ : UInt16) : Nat := 2
instance : GetByteSize UInt16 where byteSize := UInt16.byteSize

/- ========================================================================= -/
/-! ## 32-bit Unsigned Integer (`UInt32`) -/

def UInt32.serialize (n : UInt32) : List UInt8 :=
  let b1 := (n >>> 24).toUInt8
  let b2 := (n >>> 16).toUInt8
  let b3 := (n >>> 8).toUInt8
  let b4 := n.toUInt8
  [b1, b2, b3, b4]

def UInt32.parser : Parser UInt32 := do
  let b1 ← UInt8.parser
  let b2 ← UInt8.parser
  let b3 ← UInt8.parser
  let b4 ← UInt8.parser
  return (b1.toUInt32 <<< 24) |||
         (b2.toUInt32 <<< 16) |||
         (b3.toUInt32 <<< 8)  |||
          b4.toUInt32

instance : Codec UInt32 where
  parser := UInt32.parser
  serialize := UInt32.serialize

@[simp] def UInt32.byteSize (_ : UInt32) : Nat := 4
instance : GetByteSize UInt32 where byteSize := UInt32.byteSize

end Mqtt

instance : Coe UInt16 Nat where
  coe := UInt16.toNat
instance : Coe UInt32 Nat where
  coe := UInt32.toNat
