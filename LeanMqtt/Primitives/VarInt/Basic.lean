import LeanMqtt.Primitives.UInt.Basic
import LeanMqtt.Core.Codec

namespace Mqtt

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
  -- We use an accumulator loop to handle the little-endian decoding
  -- mult: The current place value (1, 128, 128^2, ...)
  -- acc:  The accumulated value so far
  -- fuel: Max bytes to read (4)
  let mul_start := 1
  let acc_start := 0
  let max_bytes := 4
  let rec loop (mult : Nat) (acc : Nat) (fuel : Nat) : Parser VarInt := do
    match fuel with
    | 0 => failure -- Exceeded 4 bytes
    | fuel' + 1 =>
      let b ← UInt8.parser

      -- The spec forbids non-minimal encodings (MQTT-1.5.5-1)
      if b = 0 ∧ fuel' < (max_bytes - 1) then
        failure

      let val := (b.toNat % 128) * mult + acc

      -- If the continuation bit is 1, keep looping
      if ¬(b < 128) then
        return ← loop (mult * 128) val fuel'

      -- The following check is always true. We do it to get a proof that
      -- the value fits on a `VarInt`.
      -- A different implementation without this check, along with a
      -- performance comparison, is available at
      -- https://gist.github.com/edusporto/2e995ccda37ab0949de03ab30da3ef49.
      -- The performance improvement was too small to justify the added
      -- complexity.
      if h_lim : val < VarInt.limit then
        return ⟨val, h_lim⟩
      else
        failure

  loop mul_start acc_start max_bytes

instance : Codec VarInt where
  parser := VarInt.parser
  serialize := VarInt.serialize

end Mqtt
