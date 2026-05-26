class GetByteSize (α : Type u) where
  byteSize : α → Nat

/-- The length of a string in MQTT is the number of bytes it contains. -/
@[reducible]
instance instStringByteLength : GetByteSize String where
  byteSize s := s.utf8ByteSize

@[reducible]
instance : GetByteSize (Array UInt8) where
  byteSize := Array.size

-- class LengthEmbedding (lenTyp : Type) where
--   toNat : lenTyp → Nat
--   injective : Function.Injective toNat

structure WithByteSize (α lenTyp) [s : GetByteSize α] [Coe lenTyp Nat] where
  val : α
  -- TODO: `Coe lenTyp Nat`, possible point of failure?
  -- Example: for lenTyp = Int, `-5`.toNat.toInt ≠ `-5`
  -- Fix: use LengthEmbedding instead of `Coe lenTyp Nat`
  len : { n : lenTyp // n = s.byteSize val }

@[simp]
theorem WithByteSize.len_eq {α lenTyp} [GetByteSize α] [Coe lenTyp Nat]
    (w : WithByteSize α lenTyp) :
    ↑w.len.val = GetByteSize.byteSize w.val :=
  w.len.property
