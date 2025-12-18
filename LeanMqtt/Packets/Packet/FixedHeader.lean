import LeanMqtt.Primitives
import LeanMqtt.Serialization

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

private instance (r : Std.Range) (i : Nat) : Decidable (i ∈ r) := by
  dsimp [Membership.mem]
  infer_instance

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

theorem WhichPkt.encode_decode (which : WhichPkt) :
  WhichPkt.decode? which.encode = which := by
  cases which <;> rfl

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

structure FixedHeader where
  which : WhichPkt
  flags : WhichPkt.flagType which
  size  : VarInt -- TODO: depend on information after

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

theorem WhichPkt.encode_decode_flags (which : WhichPkt) (flags : WhichPkt.flagType which) :
  WhichPkt.decodeFlags which (WhichPkt.encodeFlags which flags) = some flags := by
  cases which <;> simp [encodeFlags, decodeFlags]
  case publish =>
    have h₁ : BitVec.extractLsb 3 3 (flags.dup ++ flags.qos ++ flags.retain) = flags.dup := by bv_decide
    have h₂ : BitVec.extractLsb 2 1 (flags.dup ++ flags.qos ++ flags.retain) = flags.qos := by bv_decide
    have h₃ : BitVec.extractLsb 0 0 (flags.dup ++ flags.qos ++ flags.retain) = flags.retain := by bv_decide
    rw [h₁, h₂, h₃]
    rfl
  all_goals {
    have : flags.val = _ := flags.property
    simp only [this, BitVec.ofNat_eq_ofNat, exists_true_left]
    exact Subtype.ext flags.property.symm
  }

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

theorem WhichPkt.roundtrip (which : WhichPkt) (flags : WhichPkt.flagType which) (rest : List UInt8) :
  WhichPkt.parser.run (WhichPkt.serialize which flags ++ rest) = some (⟨which, flags⟩, rest) := by
  simp only [WhichPkt.parser, WhichPkt.serialize,]
  simp only [
    bind_pure_comp, BitVec.append_eq, Nat.reduceAdd, StateT.run_bind,
    StateT.run_monadLift, monadLift_self, Option.pure_def, Option.bind_eq_bind,
    Option.bind, StateT.run_map, Option.map_eq_map
  ]
  simp only [UInt8.roundtrip _ _]
  have : BitVec.extractLsb 7 4 (which.encode ++ which.encodeFlags flags) = which.encode :=
    by bv_decide
  rw [this]
  simp [WhichPkt.encode_decode]
  have : BitVec.extractLsb 3 0 (which.encode ++ which.encodeFlags flags) = which.encodeFlags flags :=
    by bv_decide
  rw [this]
  simp [WhichPkt.encode_decode_flags]

def FixedHeader.serialize : FixedHeader → List UInt8 :=
  fun ⟨which, flags, size⟩ =>
    let byte1 := which.serialize flags
    byte1 ++ (VarInt.serialize size)

def FixedHeader.parser : Parser FixedHeader := do
  let ⟨which, flags⟩ ← WhichPkt.parser
  let size ← VarInt.parser
  return { which, flags, size }

theorem FixedHeader.roundtrip (header : FixedHeader) (rest : List UInt8) :
  FixedHeader.parser.run (header.serialize ++ rest) = some (header, rest) := by
  simp [FixedHeader.parser, FixedHeader.serialize]
  simp [WhichPkt.roundtrip header.which header.flags]
  simp [VarInt.roundtrip _]
