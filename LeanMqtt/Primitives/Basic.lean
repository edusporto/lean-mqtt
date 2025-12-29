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

-- def VarInt.parser : Parser VarInt := do
--   -- We use an accumulator loop to handle the Little-Endian decoding
--   -- mult: The current place value (1, 128, 128^2, ...)
--   -- acc:  The accumulated value so far
--   -- fuel: Max bytes to read (4)
--   let rec loop (mult : Nat) (acc : Nat) (fuel : Nat) : Parser VarInt := do
--     match fuel with
--     | 0 => none -- Exceeded 4 bytes (Malformed Packet)
--     | fuel' + 1 =>
--       let b ← UInt8.parser
--       let val := (b % 128).toNat * mult + acc

--       if b < 128 then
--         -- Continuation bit is 0: We are done.
--         -- Check if the result fits in the VarInt limit.
--         if h : val < VarInt.limit then
--           some ⟨val, h⟩
--         else
--           none -- Value exceeds protocol limit
--       else
--         -- Continuation bit is 1: Keep reading.
--         loop (mult * 128) val fuel'

--   loop 1 0 4

def VarInt.parser : Parser VarInt := do
  -- We add two proof arguments (h_inv and h_acc) to the loop.
  -- These are erased at runtime but allow us to prove safety.
  let rec loop (mult : Nat) (acc : Nat) (fuel : Nat)
      (h_inv : mult * 128 ^ fuel = VarInt.limit)
      (h_acc : acc < mult) : Parser VarInt := do
    match fuel with
    | 0 => none -- Malformed Packet (Too many bytes)
    | fuel' + 1 =>
      -- 1. Setup the math for the next step
      -- We know mult * 128^(fuel' + 1) = limit.
      -- Rewrite this to (mult * 128) * 128^fuel' = limit
      have h_next_inv : (mult * 128) * 128 ^ fuel' = VarInt.limit := by
        rw [Nat.pow_succ, ←Nat.mul_assoc] at h_inv
        grind only

      -- 2. Read the byte
      let b ← UInt8.parser
      let n := (b % 128).toNat

      -- 3. Calculate new value: val = n * mult + acc
      let val := n * mult + acc

      -- 4. Prove that the new value fits within the next multiplier scope.
      -- We need to prove: val < mult * 128
      have h_val_bound : val < mult * 128 := by
        -- We know n < 128, so n ≤ 127
        have h_n : n ≤ 127 := by
          have : n < 128 := Nat.mod_lt (b.toNat) (by decide : 0 < 128)
          omega
        -- val = n * mult + acc ≤ 127 * mult + acc
        -- Since acc < mult, val < 127 * mult + mult = 128 * mult
        calc
          n * mult + acc ≤ 127 * mult + acc := Nat.add_le_add_right (Nat.mul_le_mul_right mult h_n) acc
          _              < 127 * mult + mult := Nat.add_lt_add_left h_acc _
          _              = 128 * mult        := by simp [Nat.succ_mul, Nat.add_comm]
          _              = mult * 128        := Nat.mul_comm _ _

      if b < 128 then
        -- Continuation bit is 0: We are done.
        -- We need to return `Fin VarInt.limit`.
        -- We must prove `val < VarInt.limit`.
        have h_final : val < VarInt.limit := by
          -- We know val < mult * 128
          -- We know (mult * 128) * 128^fuel' = limit
          -- Therefore (mult * 128) ≤ limit (since 128^fuel' ≥ 1)
          apply Nat.lt_of_lt_of_le h_val_bound
          have h_scale : 1 ≤ 128 ^ fuel' := Nat.one_le_pow fuel' 128 (by decide)
          have h_mult_le : mult * 128 ≤ VarInt.limit := by
            rw [←h_next_inv]
            exact Nat.le_mul_of_pos_right _ h_scale
          exact h_mult_le

        -- Return the value directly constructed with the proof
        some ⟨val, h_final⟩
      else
        -- Continuation bit is 1: Keep reading.
        loop (mult * 128) val fuel' h_next_inv h_val_bound

  -- Initial call:
  -- mult = 1, acc = 0, fuel = 4
  -- Proof 1: 1 * 128^4 = VarInt.limit (True by definition)
  -- Proof 2: 0 < 1 (True)
  loop 1 0 4 (by rfl) (by decide)

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
