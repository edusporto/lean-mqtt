import LeanMqtt.WithLength
import LeanMqtt.Serialization

instance : Coe UInt16 Nat where
  coe := UInt16.toNat
instance : Coe UInt32 Nat where
  coe := UInt32.toNat

abbrev Str := WithLength String UInt16

def Str.serialize (s : Str) : List UInt8 :=
  UInt16.serialize (s.len) ++ s.val.serialize

def Str.parser : Parser Str := do
  let len ← UInt16.parser
  let ⟨str, h⟩ ← String.parserWithProof len.toNat

  have h_len : Coe.coe len = GetLength.length str := by
    simp [Coe.coe, GetLength.length]; exact h.symm

  return {val := str, len := ⟨len, h_len⟩ }

theorem Str.roundtrip (s : Str) (rest : List UInt8) :
  Str.parser.run (s.serialize ++ rest) = some (s, rest) := by
  simp only [Str.parser, Str.serialize]
  simp only [
    bind_pure_comp, List.append_assoc, StateT.run_bind, StateT.run_map,
    Option.map_eq_map, Option.bind_eq_bind
  ]

  rw [UInt16.roundtrip _ _]
  simp only [Option.bind_some, Option.map]

  have h_len_eq : s.len.val.toNat = s.val.serialize.length := by
    rw [String.serialize_len]
    have h := s.len.property
    -- simp [Coe.coe, GetLength.length] at h
    exact h

  /-
    To use the String.roundtrip theorem, we need to substitute `s.len.val.toNat`
    with `s.val.serialize.length`. However, due to dependent type shenanigans,
    we can't do this substitution in `String.parserWithProof`. So, we do the
    substitution in the simple parser (`String.parser`), then use the projection
    lemma (`String.parserWithProof_eq_parser_success`) to show it also holds for
    `String.parserWithProof`.
  -/
  have h_simple := String.roundtrip s.val rest

  rw [←h_len_eq] at h_simple
  have ⟨_, h_dep⟩ := String.parserWithProof_eq_parser_success _ _ _ _ h_simple

  rw [h_dep]

abbrev StrPair := Str × Str

def StrPair.serialize (p : StrPair) : List UInt8 :=
  p.fst.serialize ++ p.snd.serialize

def StrPair.parser : Parser StrPair := do
  let s1 ← Str.parser
  let s2 ← Str.parser
  return ⟨s1, s2⟩

theorem StrPair.roundtrip (p : StrPair) (rest : List UInt8) :
  StrPair.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp only [StrPair.parser, StrPair.serialize]
  simp only [
    bind_pure_comp, List.append_assoc, StateT.run_bind, StateT.run_map,
    Option.map_eq_map, Option.map, Option.bind_eq_bind, Option.bind
  ]
  simp only [Str.roundtrip _ _]

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

theorem BinaryData.roundtrip (b : BinaryData) (rest : List UInt8) :
  BinaryData.parser.run (b.serialize ++ rest) = some (b, rest) := by
  simp only [BinaryData.parser, BinaryData.serialize]
  simp [Option.bind, Option.map]

  rw [UInt16.roundtrip _ _]
  simp only

  have h_len_eq : b.len.val.toNat = b.val.toList.length := by
    simp only [Array.length_toList]
    have h := b.len.property
    exact h

  /-
    Due to dependent type shenanigans, we can't rewrite the current goal
    with `h_len_eq`. So, we rewrite it in the simpler parser, and prove
    that it implies our current goal. See `Str.roundtrip` for more.
  -/
  have h_simple := roundtrip_bytes b.val.toList rest
  rw [←h_len_eq] at h_simple
  have ⟨_, h_dep⟩ := bytesParserWithProof_eq_parser_success _ _ _ _ h_simple

  rw [h_dep]

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
  coe v := v.toNat

def VarInt.serialize (v : VarInt) : List UInt8 :=
  if h : v < 128 then
    [v.val.toUInt8]
  else
    let byte := ((v.val % 128) + 128).toUInt8
    byte :: VarInt.serialize (v / 128)
termination_by v.val
decreasing_by
  -- We need to prove: v.val / 128 < v.val
  -- We know 'h' is false, so v.val >= 128
  simp only [Fin.isValue, Fin.not_lt] at h
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
      let val := (b.toNat % 128) * mult + acc

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

-- TODO: this proof is beyond my pay grade
theorem VarInt.roundtrip (v : VarInt) (rest : List UInt8) :
  VarInt.parser.run (v.serialize ++ rest) = some (v, rest) :=
  sorry

/--
  Executable checker: Returns true if 'n' survives the roundtrip.
  Note: We use strict equality checks.
-/
def checksOut (n : VarInt) : Bool :=
  let bytes := VarInt.serialize n
  match VarInt.parser.run bytes with
  | some (v, []) => v.val == n
  | _ => false

/-- Checks 'checksOut' for all numbers from 'start' up to 'limit' -/
def checkRange (start limit : Nat) : Bool :=
  if start >= limit then
    true
  else if h : ¬(start < VarInt.limit) then
    false
  else if checksOut ⟨start, Decidable.of_not_not h⟩ then
    checkRange (start + 1) limit
  else
    false

-- max: 268_435_456
-- theorem VarInt.roundtrip_exhaust_16384 : checkRange 0 16384 = true := by
--   native_decide

/-
theorem VarInt.roundtrip_lt_128 (n : Nat) (h : n < 128) (rest : List UInt8) :
  let v : VarInt := ⟨n, Nat.lt_trans h (by decide)⟩
  VarInt.parser.run (VarInt.serialize v ++ rest) = some (v, rest) := by
  simp [VarInt.parser, VarInt.serialize, h, StateT.run]
  simp [parser.loop, bind, StateT.bind, Option.bind]
  split
  { next _ h_wrong =>
    rw [parser_app_is_run parseByte] at h_wrong
    rw [roundtrip_byte _] at h_wrong
    contradiction
   }
  { next x h₁ =>
    simp only
    rw [parser_app_is_run parseByte] at h₁
    rw [roundtrip_byte _] at h₁
    injection h₁ with h₁
    rw [←h₁]
    simp only
    have : UInt8.ofNat n < 128 := by
      simp [UInt8.ofNat]
      simp only [UInt8.lt_iff_toNat_lt]
      simp only [UInt8.toNat_ofNat]
      omega
    simp only [if_pos this]
    simp only [UInt8.toNat_ofNat', Nat.reducePow, Nat.reduceDvd, Nat.mod_mod_of_dvd]
    simp [@Nat.mod_eq_of_lt n 128 h]
    have : n < limit := Nat.lt_trans h (by decide)
    simp only [dif_pos (this)]
    simp [liftM, monadLift, MonadLift.monadLift, StateT.lift]
   }
-/

-- theorem VarInt.roundtrip_lt_16384 (n : Nat) (h₁ : 127 < n) (h₂ : n < 16384) (rest : List UInt8) :
--   let v : VarInt := ⟨n, Nat.lt_trans h₂ (by decide)⟩
--   VarInt.parser.run (VarInt.serialize v ++ rest) = some (v, rest) := by
--   sorry

-- theorem VarInt.roundtrip_lt_16384 (n : Nat) (h₁ : 127 < n) (h₂ : n < 16384) (rest : List UInt8) :
--   let v : VarInt := ⟨n, Nat.lt_trans h₂ (by decide)⟩
--   VarInt.parser.run (VarInt.serialize v ++ rest) = some (v, rest) := by
--   -- 1. Establish Arithmetic Facts
--   have h_not_lt_128 : ¬ (n < 128) := by omega
--   have h_div_lt_128 : n / 128 < 128 := by
--     apply Nat.div_lt_of_lt_mul; exact h₂
--   let v : VarInt := ⟨n, Nat.lt_trans h₂ (by decide)⟩

--   -- 2. Expand Serialization Safely (Avoiding infinite simp loop)
--   unfold VarInt.serialize
--   simp only [h_not_lt_128, ite_false]
--   unfold VarInt.serialize
--   simp only [h_div_lt_128, ite_true]

--   -- The term is now explicit: [byte1, byte2] ++ rest.
--   -- We prove properties about these specific bytes for the parser.

--   -- Byte 1 is the continuation byte (>= 128)
--   have b1_is_continuation : ¬ (((n % 128) + 128).toUInt8 < 128) := by
--     simp [UInt8.toNat_ofNat]
--     have : (n % 128) + 128 < 256 := by omega
--     simp [Nat.mod_eq_of_lt this]
--     omega

--   -- Byte 2 is the final byte (< 128)
--   have b2_is_final : (n / 128).toUInt8 < 128 := by
--     simp [UInt8.toNat_ofNat]
--     rw [Nat.mod_eq_of_lt (Nat.lt_trans h_div_lt_128 (by decide))]
--     exact h_div_lt_128

--   -- 3. Execute the Parser Step-by-Step
--   --    We use 'simp' to run the Monad logic, but we must manually unroll 'decodeLoop'.
--   simp only [VarInt.parser, StateT.run, Option.bind]

--   -- Unroll Loop 1 (Fuel 4 -> 3)
--   rw [VarInt.decodeLoop]
--   simp [parseByte] -- Consumes first byte
--   simp [b1_is_continuation] -- Enters 'else' branch

--   -- Unroll Loop 2 (Fuel 3 -> 2)
--   rw [VarInt.decodeLoop]
--   simp [parseByte] -- Consumes second byte
--   simp [b2_is_final] -- Enters 'if' branch (termination)

--   -- 4. Verify the Result
--   --    The parser output is: ((byte2 % 128) * 128 + (byte1 % 128))
--   simp only [UInt8.toNat_ofNat]

--   -- Simplify modulo arithmetic
--   have mod_identity : ((n % 128) + 128) % 128 = n % 128 := by omega
--   have div_identity : (n / 128) % 128 = n / 128 := Nat.mod_eq_of_lt h_div_lt_128

--   simp [mod_identity, div_identity]

--   -- Prove reconstruction: (n / 128) * 128 + n % 128 = n
--   rw [Nat.mul_comm, Nat.div_add_mod]

--   -- Final check: the value fits in the limit
--   simp [Nat.lt_trans h₂ (by decide)]
--   rfl

-- theorem VarInt.roundtrip :
--   ∀i : VarInt, some i = Option.map fst (VarInt.decode? (i.encode) 0) :=
--   by sorry

-- /-!
-- # Proof Strategy: Unrolling
-- Instead of induction or brute force, we split the domain into the 4 possible
-- byte-lengths. We define a helper tactic to unroll the loop one layer at a time.
-- -/

-- /--
--   Tactic to perform one step of unrolling for both the Serializer and the Parser.
--   It:
--   1. Expands 'serialize' once (using the fact that n >= 128).
--   2. Expands 'parser' loop once (consuming that byte).
--   3. Simplifies the accumulator math.
-- -/
-- macro "step_unroll" : tactic => `(tactic| {
--   -- 1. Unroll Serialization
--   -- We rely on the context having a hypothesis that n >= 128
--   conv in (VarInt.serialize _) =>
--     rw [VarInt.serialize]
--     simp [Nat.not_lt_of_le (by assumption)] -- Enters 'else' branch

--   -- 2. Unroll Parser Loop
--   -- Expand the definition of the loop once
--   rw [VarInt.decodeLoop]

--   -- 3. Execute the Parse Step
--   -- This consumes the byte we just serialized
--   simp only [parseByte, StateT.run, Option.bind, bind]

--   -- 4. Clean up Arithmetic
--   -- Prove the byte we wrote >= 128 (continuation bit set)
--   simp only [UInt8.toNat_ofNat]
--   try simp [Nat.mod_eq_of_lt (Nat.lt_trans (by assumption) (by decide))]
-- })

-- /-- The Main Roundtrip Theorem -/
-- theorem VarInt.roundtrip_all (n : Nat) (h : n < VarInt.limit) (rest : List UInt8) :
--   let v : VarInt := ⟨n, h⟩
--   VarInt.parser.run (VarInt.serialize v ++ rest) = some (v, rest) := by

--   -- Define the bounds for readability
--   let b1 := 128
--   let b2 := 16384     -- 128^2
--   let b3 := 2097152   -- 128^3

--   -- SPLIT 1: Is it 1 byte or more?
--   if h1 : n < b1 then
--     -- CASE: 1 Byte (n < 128)
--     -- Just expand definitions once.
--     unfold VarInt.serialize
--     simp only [h1, ite_true]
--     rw [VarInt.parser, VarInt.parser.loop]
--     simp [parseByte]
--     simp [StateT.run]
--     -- The parser sees byte < 128, checks limit, and returns.
--     simp [h1, h]

--   else
--     -- SPLIT 2: Is it 2 bytes or more?
--     push_neg at h1 -- We know n >= 128
--     if h2 : n < b2 then
--       -- CASE: 2 Bytes (128 <= n < 16384)
--       -- Unroll Layer 1
--       step_unroll

--       -- We are now left with the recursive call for (n / 128).
--       -- Since n < 128^2, (n / 128) < 128. This is now a 1-byte case!

--       -- Finish with base logic
--       simp [VarInt.decodeLoop, VarInt.serialize, parseByte]
--       -- Prove (n / 128) < 128
--       have : n / 128 < 128 := Nat.div_lt_of_lt_mul h2
--       simp [this]
--       -- Prove Arithmetic reconstruction: (n/128)*128 + n%128 = n
--       exact Nat.div_add_mod n 128

--     else
--       -- SPLIT 3: Is it 3 bytes or more?
--       push_neg at h2 -- We know n >= 16384
--       if h3 : n < b3 then
--         -- CASE: 3 Bytes
--         step_unroll -- Layer 1
--         step_unroll -- Layer 2

--         -- Finish with base logic (final byte)
--         simp [VarInt.decodeLoop, VarInt.serialize, parseByte]
--         -- Prove final byte is small
--         have : n / 128 / 128 < 128 := by
--           repeat apply Nat.div_lt_of_lt_mul
--           exact h3
--         simp [this]
--         -- Arithmetic
--         ring_nf -- Solves the (a*128 + b)*128 + c = n algebra
--         exact Nat.div_add_mod n 128

--       else
--         -- CASE: 4 Bytes
--         push_neg at h3 -- We know n >= 2097152

--         step_unroll -- Layer 1
--         step_unroll -- Layer 2
--         step_unroll -- Layer 3

--         -- Finish with base logic
--         simp [VarInt.decodeLoop, VarInt.serialize, parseByte]
--         have : n / 128 / 128 / 128 < 128 := by
--           repeat apply Nat.div_lt_of_lt_mul
--           exact h
--         simp [this]

--         -- The arithmetic here is: (((n/128)/128)/128)*128...
--         -- Just chain the div_add_mod lemma
--         conv => rhs; rw [←Nat.div_add_mod n 128]
--         conv => rhs; arg 1; arg 1; rw [←Nat.div_add_mod (n/128) 128]
--         conv => rhs; arg 1; arg 1; arg 1; arg 1; rw [←Nat.div_add_mod (n/128/128) 128]
--         rfl
