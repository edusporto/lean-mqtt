import LeanMqtt.Core.Parser.Basic
import LeanMqtt.Core.WithLength

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
  let bytes ← bytesParser 2
  match bytes with
  | [b1, b2] => return (b1.toUInt16 <<< 8) ||| b2.toUInt16
  | _ => none

/- ========================= UInt32 ========================= -/

def UInt32.serialize (n : UInt32) : List UInt8 :=
  let b1 := (n >>> 24).toUInt8
  let b2 := (n >>> 16).toUInt8
  let b3 := (n >>> 8).toUInt8
  let b4 := n.toUInt8
  [b1, b2, b3, b4]

def UInt32.parser : Parser UInt32 := do
  let bytes ← bytesParser 4
  match bytes with
  | [b1, b2, b3, b4] =>
    return (b1.toUInt32 <<< 24) |||
           (b2.toUInt32 <<< 16) |||
           (b3.toUInt32 <<< 8)  |||
            b4.toUInt32
  | _ => none

/- ========================= VarInt ========================= -/

/--
  The maximum value for a
  [Variable Byte Integer](https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901011)
  is 268_435_455 (128^4 - 1).
-/
abbrev VarInt.limit : Nat := 268_435_456

/--
  Type representing a
  [Variable Byte Integer](https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901011).
-/
abbrev VarInt := Fin VarInt.limit

instance : Coe VarInt Nat where
  coe v := v.val

def VarInt.serialize (v : VarInt) : List UInt8 :=
  if h : v.val < 128 then
    [v.val.toUInt8]
  else
    let byte := v.val.toUInt8 % 128 + 128
    byte :: VarInt.serialize (v / 128)
termination_by v.val
decreasing_by
  -- We need to prove: v.val / 128 < v.val
  -- We know v.val >= 128
  simp only [Nat.not_lt] at h
  apply Nat.div_lt_self
  · exact Nat.lt_of_lt_of_le (by decide) h
  · decide

def VarInt.parser : Parser VarInt := do
  -- We use an accumulator loop to handle the Little-Endian decoding
  -- mult: The current place value (1, 128, 128^2, ...)
  -- acc:  The accumulated value so far
  -- fuel: Max bytes to read (4)
  let rec loop (mult : Nat) (acc : Nat) (fuel : Nat) : Parser VarInt := do
    match fuel with
    | 0 => none -- Exceeded 4 bytes (Malformed Packet)
    | fuel' + 1 =>
      let b ← UInt8.parser
      let val := (b % 128).toNat * mult + acc

      if b < 128 then
        -- Continuation bit is 0: We are done.
        -- Check if the result fits in the VarInt limit.
        if h : val < VarInt.limit then
          some ⟨val, h⟩
        else
          none -- Value exceeds protocol limit
      else
        -- Continuation bit is 1: Keep reading.
        loop (mult * 128) val fuel'

  loop 1 0 4

/- ========================= String ========================= -/

-- TODO: benchmark if `ByteArray.toList arr` is faster than `Array.toList arr.data`
def String.serialize (s : String) := s.toUTF8.toList

def String.parser (len : Nat) : Parser String := do
  let bytes ← bytesParser len
  let txt := bytes.toByteArray
  if h_valid : txt.IsValidUTF8
    then some (String.fromUTF8 txt h_valid)
    else none

def String.parserWithProof (n : Nat) : Parser { s : String // s.utf8ByteSize = n } := do
  let ⟨bytes, h_len⟩ ← bytesParserWithProof n
  let txt := bytes.toByteArray
  if h_valid : txt.IsValidUTF8 then
    let s := String.fromUTF8 txt h_valid

    have h_size : s.utf8ByteSize = n := by
      simp only [String.utf8ByteSize]
      simp only [s, String.fromUTF8, txt, List.size_toByteArray]
      exact h_len

    return ⟨s, h_size⟩
  else
    none

/- ========================= Str ========================= -/

abbrev Str := WithLength String UInt16

def Str.serialize (s : Str) : List UInt8 :=
  UInt16.serialize (s.len) ++ String.serialize s.val

def Str.parser : Parser Str := do
  let len ← UInt16.parser
  let ⟨str, h⟩ ← String.parserWithProof len.toNat

  have h_len : Coe.coe len = GetLength.length str := by
    simp [Coe.coe, GetLength.length]; exact h.symm

  return {val := str, len := ⟨len, h_len⟩ }

/- ========================= StrPair ========================= -/

abbrev StrPair := Str × Str

def StrPair.serialize (p : StrPair) : List UInt8 :=
  Str.serialize (p.fst) ++ Str.serialize (p.snd)

def StrPair.parser : Parser StrPair := do
  let s1 ← Str.parser
  let s2 ← Str.parser
  return ⟨s1, s2⟩

/- ========================= BinaryData ========================= -/

abbrev BinaryData := WithLength (Array UInt8) UInt16

def BinaryData.serialize (b : BinaryData) :=
  UInt16.serialize (b.len) ++ b.val.toList

def BinaryData.parser : Parser BinaryData := do
  let len ← UInt16.parser
  let ⟨l, h⟩ ← bytesParserWithProof len.toNat
  let b := l.toArray

  have h_len : Coe.coe len = GetLength.length b := by
    simp [Coe.coe, GetLength.length]; apply h.symm

  return {val := b, len := ⟨len, h_len⟩ }

end Mqtt
