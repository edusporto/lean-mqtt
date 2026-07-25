/-!
# WithByteSize

This module provides the `WithByteSize` structure, a dependent type that pairs a value with
its serialized byte size. This is particularly useful in the MQTT protocol, where many variable
length fields (like strings and binary data) are prefixed by their length.

By statically binding a value to its length with a proof `GetByteSize.byteSize val = ↑len`,
we guarantee that the prefixed length perfectly matches the actual payload size.
-/

/--
A typeclass for types that have a definable byte size when serialized.
-/
class GetByteSize (α : Type u) where
  byteSize : α → Nat

/-- The length of a string in MQTT is the number of bytes it contains in UTF-8. -/
@[reducible]
instance instStringByteLength : GetByteSize String where
  byteSize s := s.utf8ByteSize

/-- The byte size of a byte array is simply its element count. -/
@[reducible]
instance : GetByteSize (Array UInt8) where
  byteSize := Array.size

-- class LengthEmbedding (lenTyp : Type) where
--   toNat : lenTyp → Nat
--   injective : Function.Injective toNat

/--
A dependent type pairing a value of type `α` with its length of type `lenTyp`.
The `len` field contains a proof that the byte size of `val` is exactly `len.val`.
-/
structure WithByteSize (α lenTyp) [s : GetByteSize α] [Coe lenTyp Nat] where
  val : α
  -- TODO: `Coe lenTyp Nat`, possible point of failure?
  -- Example: for lenTyp = Int, `-5`.toNat.toInt ≠ `-5`
  -- Fix: use LengthEmbedding instead of `Coe lenTyp Nat`
  len : { n : lenTyp // s.byteSize val = n }
deriving DecidableEq

/-- Convenience theorem extracting the proof that the byte size of `val` equals `len`. -/
@[simp]
theorem WithByteSize.len_eq {α lenTyp} [GetByteSize α] [Coe lenTyp Nat]
    (w : WithByteSize α lenTyp) :
    GetByteSize.byteSize w.val = ↑w.len.val :=
  w.len.property

/--
  Instantiates `WithByteSize` without manually providing the length and the proof.
  The proof is solved automatically by `rfl` at the call site once the value is instantiated.

  **Example usage**:
  ```lean
  let mqttStr : Mqtt.Str := WithByteSize.of "MQTT"
  ```
-/
def WithByteSize.of {α lenTyp} [s : GetByteSize α] [Coe lenTyp Nat]
    (val : α) [OfNat lenTyp (s.byteSize val)]
    (h : s.byteSize val = ↑(OfNat.ofNat (s.byteSize val) : lenTyp) := by rfl) :
    WithByteSize α lenTyp :=
  ⟨val, ⟨OfNat.ofNat (s.byteSize val), h⟩⟩

/-!
### Note on generic binary parser generation (future DSL design)

Considering `WithByteSize` in our future generic binary parser DSL, the `Coe lenTyp Nat`
abstraction is intentionally chosen over a strict `Injective` requirement for `lenTyp → Nat`.
```lean
-- The restriction for `lenTyp` would look like:
class LengthEmbedding (lenTyp : Type) where
  toNat : lenTyp → Nat
  injective : Function.Injective toNat
```
At first, it might seem interesting to force injectivity due to cases like `lenTyp = Int`,
with `(-5).toNat.toInt ≠ -5`. However, we currently think it's best to keep the `Cpe` approach
due to the following:

1. **Overloaded bits (length + flags)**:
Many binary formats pack flags into the highest bits of a length integer. If `lenTyp`
holds both length and flags, `Coe lenTyp Nat` will intentionally not be injective (e.g.,
lengths `0x05` and `0x85` could both map to a payload size of `5`). By avoiding a strict
injectivity requirement, `WithByteSize` can bind purely to the length aspect of the bits
while allowing the underlying `lenTyp` to independently serialize/parse its auxiliary flags.

2. **Non-canonical encodings & reconstruction proofs**:
If a binary format allows multiple byte sequences to represent the same length (e.g. LEB128
with padding zeros), the parser often normalizes them. This breaks exact-byte reconstruction
(`parse(input) = v → input = serialize(v)`) for non-canonical inputs.
We could handle this lossiness in the future by one of the following:
- Proving reconstruction only on a restricted subset: `IsCanonical input → ...`
- Proving an equivalence relation instead of strict equality: `input ≈ serialize(v)`,
  where `≈` ignores padding bytes.
- Proving parsing idempotence: `parse(serialize(v)) = some (v, [])` when `parse(input) = some (v, rest)`,
  which ensures a stable parsing loop instead of completely discarding reconstruction proofs.
-/
