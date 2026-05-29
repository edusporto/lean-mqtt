import LeanMqtt.Core.WithByteSize
import LeanMqtt.Core.Codec
import LeanMqtt.Core.Parser.Basic

namespace Mqtt
open Mqtt

/- ========================= Generic List ByteSize ========================= -/

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

/- ============================== ChunkItem ================================ -/
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
  Option { ps : List α // input.length = (ps.map GetByteSize.byteSize).sum } :=
  if h_empty : input.isEmpty then
    some ⟨[], by simp; grind⟩
  else
    match h_parse : (Codec.parser : Parser α).run input with
    | some (item, rest) =>
      match parseChunkLoop rest with
      | some ⟨tail, h_tail_len⟩ =>
        let h_len_ps : input.length = ((item :: tail).map GetByteSize.byteSize).sum := by
          have h_c : input.length = GetByteSize.byteSize item + rest.length :=
            ChunkItem.h_consumed h_parse
          rw [h_tail_len] at h_c
          exact h_c

        some ⟨(item :: tail), h_len_ps⟩
      | none => none
    | none => none
termination_by input.length
decreasing_by
  have h_c := ChunkItem.h_consumed h_parse
  have h_p := ChunkItem.h_pos item
  omega

/- ============================== SizedList ================================ -/

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

  match ChunkItem.parseChunkLoop chunk with
  | some ⟨items, h_loop_len⟩ =>
    have h_len : (len : Nat) = (items.map GetByteSize.byteSize).sum := by
      rw [← h_chunk_len]
      exact h_loop_len

    return { val := items, len := ⟨len, h_len⟩ }
  | none => none
