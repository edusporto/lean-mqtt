import LeanMqtt.Core.Parser.Basic
import LeanMqtt.Core.WithByteSize

instance : Coe UInt16 Nat where
  coe := UInt16.toNat
instance : Coe UInt32 Nat where
  coe := UInt32.toNat

namespace Mqtt

/- ========================= UInt8 ========================= -/

def UInt8.serialize (b : UInt8) : List UInt8 :=
  [b]

def UInt8.parser : Parser UInt8 := do
  match (← get) with
  | [] => none
  | b :: rest =>
    set rest
    some b

/- ========================= UInt16 ========================= -/

def UInt16.serialize (n : UInt16) : List UInt8 :=
  let b1 := (n >>> 8).toUInt8
  let b2 := n.toUInt8
  [b1, b2]

def UInt16.parser : Parser UInt16 := do
  let b1 ← UInt8.parser
  let b2 ← UInt8.parser
  return (b1.toUInt16 <<< 8) ||| b2.toUInt16

/- ========================= UInt32 ========================= -/

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

end Mqtt
