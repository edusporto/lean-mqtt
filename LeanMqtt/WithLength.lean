class GetLength (α : Type u) where
  length : α → Nat

/-- In MQTT, a String's length is actually the number of bytes it contains. -/
@[reducible]
instance instStringByteLength : GetLength String where
  length s := s.utf8ByteSize

-- @[reducible]
-- instance : GetLength String where
--   length := String.length

@[reducible]
instance : GetLength (Array UInt8) where
  length := Array.size

-- @[reducible]
-- instance {α} : GetLength (Array α) where
--   length := Array.size

-- class LengthEmbedding (lenTyp : Type) where
--   toNat : lenTyp → Nat
--   injective : Function.Injective toNat

structure WithLength (α lenTyp) [s : GetLength α] [Coe lenTyp Nat] where
  val : α
  -- TODO: `Coe lenTyp Nat`, possible point of failure?
  -- Example: for lenTyp = Int, `-5`.toNat.toInt ≠ `-5`
  -- Fix: use LengthEmbedding instead of `Coe lenTyp Nat`
  len : { n : lenTyp // n = s.length val }

@[simp]
theorem WithLength.len_eq {α lenTyp} [GetLength α] [Coe lenTyp Nat]
  (w : WithLength α lenTyp) :
  ↑w.len.val = GetLength.length w.val :=
  w.len.property
