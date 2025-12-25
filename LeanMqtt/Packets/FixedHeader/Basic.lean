import LeanMqtt.Primitives.Basic

namespace Mqtt
open Mqtt

/- ========================= WhichPkt ========================= -/

inductive WhichPkt where
  | connect
  | connack
  | publish
  | puback
  | pubrec
  | pubrel
  | pubcomp
  | subscribe
  | suback
  | unsubscribe
  | unsuback
  | pingreq
  | pingresp
  | disconnect
  | auth
deriving Repr, BEq

instance : Inhabited WhichPkt where
  default := .pingreq

structure PublishFlags where
  dup : BitVec 1
  qos : BitVec 2
  retain : BitVec 1

def WhichPkt.flagType : WhichPkt → Type
  | .connect     => { i : BitVec 4 // i = 0b0000 }
  | .connack     => { i : BitVec 4 // i = 0b0000 }
  | .publish     => PublishFlags
  | .puback      => { i : BitVec 4 // i = 0b0000 }
  | .pubrec      => { i : BitVec 4 // i = 0b0000 }
  | .pubrel      => { i : BitVec 4 // i = 0b0010 }
  | .pubcomp     => { i : BitVec 4 // i = 0b0000 }
  | .subscribe   => { i : BitVec 4 // i = 0b0010 }
  | .suback      => { i : BitVec 4 // i = 0b0000 }
  | .unsubscribe => { i : BitVec 4 // i = 0b0010 }
  | .unsuback    => { i : BitVec 4 // i = 0b0000 }
  | .pingreq     => { i : BitVec 4 // i = 0b0000 }
  | .pingresp    => { i : BitVec 4 // i = 0b0000 }
  | .disconnect  => { i : BitVec 4 // i = 0b0000 }
  | .auth        => { i : BitVec 4 // i = 0b0000 }

def WhichPkt.encode (pkt : WhichPkt) : BitVec 4 :=
  match pkt with
  | .connect     => 1
  | .connack     => 2
  | .publish     => 3
  | .puback      => 4
  | .pubrec      => 5
  | .pubrel      => 6
  | .pubcomp     => 7
  | .subscribe   => 8
  | .suback      => 9
  | .unsubscribe => 10
  | .unsuback    => 11
  | .pingreq     => 12
  | .pingresp    => 13
  | .disconnect  => 14
  | .auth        => 15

def WhichPkt.decode? : BitVec 4 → Option WhichPkt
  | 1 => some .connect
  | 2 => some .connack
  | 3 => some .publish
  | 4 => some .puback
  | 5 => some .pubrec
  | 6 => some .pubrel
  | 7 => some .pubcomp
  | 8 => some .subscribe
  | 9 => some .suback
  | 10 => some .unsubscribe
  | 11 => some .unsuback
  | 12 => some .pingreq
  | 13 => some .pingresp
  | 14 => some .disconnect
  | 15 => some .auth
  | _ => none

def WhichPkt.encodeFlags (which : WhichPkt) (flags : WhichPkt.flagType which) : BitVec 4 :=
  match which with
  | .publish =>
    flags.dup
    |>.append flags.qos
    |>.append flags.retain
    | .connect     => flags.val
    | .connack     => flags.val
    | .puback      => flags.val
    | .pubrec      => flags.val
    | .pubrel      => flags.val
    | .pubcomp     => flags.val
    | .subscribe   => flags.val
    | .suback      => flags.val
    | .unsubscribe => flags.val
    | .unsuback    => flags.val
    | .pingreq     => flags.val
    | .pingresp    => flags.val
    | .disconnect  => flags.val
    | .auth        => flags.val

def WhichPkt.decodeFlags (which : WhichPkt) (flagsBv4 : BitVec 4) : Option (WhichPkt.flagType which) :=
  match which with
  | .publish =>
    let dup    := flagsBv4.extractLsb 3 3
    let qos    := flagsBv4.extractLsb 2 1
    let retain := flagsBv4.extractLsb 0 0
    some { dup, qos, retain }
  -- Flags must be 0b10
  | .pubrel | .subscribe | .unsubscribe =>
    if h : flagsBv4 = 0b0010 then some ⟨flagsBv4, h⟩ else none
  -- Flags must be 0b00
  | .connect  | .connack | .puback   | .pubrec     | .pubcomp | .suback
  | .unsuback | .pingreq | .pingresp | .disconnect | .auth =>
    if h : flagsBv4 = 0b0000 then some ⟨flagsBv4, h⟩ else none

def WhichPkt.serialize (which : WhichPkt) (flags : WhichPkt.flagType which) : List UInt8 :=
  let byte := which
    |>.encode
    |>.append (which.encodeFlags flags)
  UInt8.ofBitVec byte |>.serialize

def WhichPkt.parser : Parser ((which : WhichPkt) × WhichPkt.flagType which) := do
  let byte ← UInt8.parser
  let bv := byte.toBitVec

  let whichBits := bv.extractLsb 7 4
  let flagsBits := bv.extractLsb 3 0

  let which ← WhichPkt.decode? whichBits
  let flags ← WhichPkt.decodeFlags which flagsBits
  return ⟨which, flags⟩

/- ========================= FixedHeader ========================= -/

structure FixedHeader where
  which : WhichPkt
  flags : WhichPkt.flagType which
  size  : VarInt -- TODO: depend on information after


def FixedHeader.serialize : FixedHeader → List UInt8 :=
  fun ⟨which, flags, size⟩ =>
    let byte1 := which.serialize flags
    byte1 ++ (VarInt.serialize size)

def FixedHeader.parser : Parser FixedHeader := do
  let ⟨which, flags⟩ ← WhichPkt.parser
  let size ← VarInt.parser
  return { which, flags, size }

end Mqtt
