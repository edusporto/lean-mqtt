import LeanMqtt.Core.WithByteSize
import LeanMqtt.Core.Codec
import LeanMqtt.Core.Parser.Basic

namespace Mqtt
open Mqtt

/-!
# Sized Lists

This module provides the generic `SizedList` primitive for parsing and serializing
variable-length lists of items where the total byte length is prefixed in the
payload (as is common in MQTT properties and payloads). It establishes the proofs
necessary to guarantee parsing termination and length correctness.
-/

/- ========================================================================= -/
/-! ## Generic List ByteSize -/

/--
Computes the total byte size of a list by summing the byte sizes of its elements.
-/
abbrev List.rawByteSize {α : Type} [GetByteSize α] (l : List α) : Nat :=
  (l.map GetByteSize.byteSize).sum

/--
Automatically provides a `GetByteSize` implementation for any list
whose elements implement `GetByteSize`.
-/
instance instGetByteSizeList {α : Type} [GetByteSize α] : GetByteSize (List α) where
  byteSize := List.rawByteSize

/- ========================================================================= -/
/-! ## Chunk Items (`ChunkItem`) -/
/--
A typeclass bundling the proofs required to safely parse a chunk inside a bounded loop.
-/
class ChunkItem (α : Type) [GetByteSize α] [c : Codec α] where
  -- Size properties to ensure correctness and termination
  h_pos : ∀ (a : α), 0 < GetByteSize.byteSize a
  h_consumed : ∀ {a : α} {input rest : List UInt8},
    c.parser.run input = some (a, rest) → input.length = GetByteSize.byteSize a + rest.length

/--
Recursively parses items of type `α` from a bounded sequence of bytes.
Returns the list of parsed items along with a proof that the sum of their
byte sizes exactly matches the original length of the input.
-/
def ChunkItem.parseChunkLoop {α : Type} [GetByteSize α] [Codec α] [ChunkItem α]
    (input : List UInt8) :
    Option { ps : List α // input.length = (ps.map GetByteSize.byteSize).sum } := do
  if h_empty : input.isEmpty then
    return ⟨[], by simp [List.nil_of_isEmpty h_empty]⟩
  else
    match h_parse : (Codec.parser : Parser α).run input with
    | some (item, rest) =>
      let ⟨tail, h_tail_len⟩ ← parseChunkLoop rest

      let h_len_ps : input.length = ((item :: tail).map GetByteSize.byteSize).sum := by
        have h_c : input.length = GetByteSize.byteSize item + rest.length :=
          ChunkItem.h_consumed h_parse
        rw [h_tail_len] at h_c
        exact h_c

      return ⟨(item :: tail), h_len_ps⟩
    | none => none
termination_by input.length
decreasing_by
  have h_c := ChunkItem.h_consumed h_parse
  have h_p := ChunkItem.h_pos item
  omega

/- ========================================================================= -/
/-! ## Sized List Definition (`SizedList`) -/

/--
List of items preceeded by the sum of their byte sizes.
Transparently resolves to `WithByteSize (List α) lenTyp`.
-/
abbrev SizedList (α lenTyp : Type) [GetByteSize α] [Coe lenTyp Nat] :=
  WithByteSize (List α) lenTyp

/--
Serializes a `SizedList` using a `Codec` for the length prefix
and `ChunkItem` for the elements.
-/
def SizedList.serialize {α lenTyp : Type}
    [GetByteSize α] [Coe lenTyp Nat] [Codec α] [ChunkItem α] [Codec lenTyp]
    (sl : SizedList α lenTyp) : List UInt8 :=
  Codec.serialize sl.len.val ++ sl.val.flatMap Codec.serialize

/--
Parses a `SizedList` with a `Codec` length prefix and `ChunkItem` elements
-/
def SizedList.parser {α lenTyp : Type}
  [GetByteSize α] [Codec α] [ChunkItem α] [Coe lenTyp Nat] [Codec lenTyp] :
  Parser (SizedList α lenTyp) := do

  let len : lenTyp ← Codec.parser
  let ⟨chunk, h_chunk_len⟩ ← Parser.bytesWithProof (len : Nat)

  let ⟨items, h_loop_len⟩ ← ChunkItem.parseChunkLoop chunk
  have h_len : (items.map GetByteSize.byteSize).sum = len := by
    rw [← h_loop_len]
    exact h_chunk_len

  return { val := items, len := ⟨len, h_len⟩ }
