import LeanMqtt.Core.Parser.Proofs
import LeanMqtt.Helpers.ParserTactics
import LeanMqtt.Primitives.SizedList.Basic

namespace Mqtt
open Mqtt

theorem ChunkItem.serialize_length {α : Type}
    [GetByteSize α] [Codec α] [LawfulCodec α] [ChunkItem α] (a : α) :
    (Codec.serialize a).length = GetByteSize.byteSize a := by
  have h_rt := LawfulCodec.roundtrip a (rest := [])
  have h_c := ChunkItem.h_consumed h_rt
  simp at h_c
  exact h_c

theorem ChunkItem.serialize_list_length {α : Type}
    [GetByteSize α] [Codec α] [LawfulCodec α] [ChunkItem α] (l : List α) :
    (l.flatMap Codec.serialize).length = List.rawByteSize l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append]
    rw [ChunkItem.serialize_length a]
    rw [ih]
    rfl

theorem ChunkItem.serialize_not_empty {α : Type}
    [GetByteSize α] [Codec α] [LawfulCodec α] [ChunkItem α] (a : α) (rest : List UInt8) :
    (Codec.serialize a ++ rest).isEmpty = false := by
  cases h : Codec.serialize a ++ rest with
  | nil =>
    have h_len : (Codec.serialize a ++ rest).length = 0 := by rw [h]; rfl
    have h_pos := ChunkItem.h_pos a
    have h_a_len := ChunkItem.serialize_length a
    rw [List.length_append, h_a_len] at h_len
    omega
  | cons _ _ => rfl

theorem ChunkItem.parseChunkLoop_roundtrip {α : Type}
    [s : GetByteSize α] [Codec α] [LawfulCodec α] [c : ChunkItem α] (l : List α) :
    ∃ h, ChunkItem.parseChunkLoop (l.flatMap Codec.serialize) = some ⟨l, h⟩ := by
  induction l with
  | nil =>
    simp [List.flatMap_nil]
    unfold ChunkItem.parseChunkLoop
    simp
  | cons a as ih =>
    have h_input :
        (a :: as).flatMap Codec.serialize
      = Codec.serialize a ++ as.flatMap Codec.serialize := rfl
    rw [h_input]

    unfold ChunkItem.parseChunkLoop

    have h_not_empty := ChunkItem.serialize_not_empty a (as.flatMap Codec.serialize)
    simp [h_not_empty]

    have h_rt := LawfulCodec.roundtrip a (rest := as.flatMap Codec.serialize)

    split
    · next item rest h_parse_eq =>
      rw [h_rt] at h_parse_eq

      injection h_parse_eq with h_pair_eq
      injection h_pair_eq with h_item h_rest

      subst h_item
      subst h_rest

      obtain ⟨h_ih_proof, h_ih_eq⟩ := ih
      rw [h_ih_eq]

      exact ⟨by simp [ChunkItem.serialize_length], rfl⟩
    · next h_parse_eq =>
      rw [h_rt] at h_parse_eq
      contradiction

theorem ChunkItem.parseChunkLoop_reconstruct {α : Type}
    [GetByteSize α] [Codec α] [LawfulCodec α] [ChunkItem α]
    {chunk : List UInt8} {items : List α}
    (h_len : chunk.length = (items.map GetByteSize.byteSize).sum) :
    ChunkItem.parseChunkLoop chunk = some ⟨items, h_len⟩ →
    chunk = items.flatMap Codec.serialize := by

  -- Induct structurally over the output list, generalizing the chunk and its length proof
  -- so the induction hypothesis applies to the remaining `mid` chunk.
  induction items generalizing chunk with
  | nil =>
    intro _ -- h_parse
    simp only [List.map_nil, List.sum_nil, List.flatMap_nil] at h_len ⊢
    cases chunk with
    | nil => rfl
    | cons hd tl => simp at h_len
  | cons a as ih =>
    intro h_parse
    unfold ChunkItem.parseChunkLoop at h_parse
    split at h_parse
    · -- Case 1: chunk is empty
      next h_empty =>
        -- The parser returned `[]`, but we assumed it equals `a :: as`.
        injection h_parse with h_eq
        injection h_eq with h_contra
        contradiction
    · -- Case 2: chunk is not empty, parse single item
      next h_not_empty =>
        split at h_parse
        · -- Item parse succeeded
          next item mid h_item_parse =>
            step_option h_parse → tail_val h_tail_parse
            obtain ⟨tail, h_tail_len⟩ := tail_val

            simp at h_parse
            obtain ⟨h_a, h_as⟩ := h_parse
            subst h_a h_as

            -- Reconstruct the head
            have h_rec_item := LawfulCodec.reconstruct h_item_parse

            -- Use the induction hypothesis for the tail directly
            have h_rec_tail := ih h_tail_len h_tail_parse

            -- Substitute and finish
            rw [h_rec_item, h_rec_tail]
            simp [List.flatMap_cons]
        · contradiction

theorem SizedList.roundtrip {α lenTyp : Type}
    [GetByteSize α] [Codec α] [LawfulCodec α] [ChunkItem α]
    [Coe lenTyp Nat] [Codec lenTyp] [LawfulCodec lenTyp]
    (sl : SizedList α lenTyp) {rest : List UInt8} :
    SizedList.parser.run (SizedList.serialize sl ++ rest) = some (sl, rest) := by

  simp [SizedList.parser, SizedList.serialize, Option.bind]

  rw [LawfulCodec.roundtrip sl.len.val]
  simp

  have h_len_eq : (sl.val.flatMap Codec.serialize).length = sl.len.val := by
    rw [ChunkItem.serialize_list_length]
    exact sl.len_eq

  -- Bypass dependent type shenanigans on the byte parser
  have h_simple := Parser.bytes_roundtrip (sl.val.flatMap Codec.serialize) rest
  rw [h_len_eq] at h_simple
  have ⟨_, h_dep⟩ := Parser.bytes_imp_bytesWithProof h_simple

  rw [h_dep]
  simp

  have ⟨h_loop_proof, h_loop_eq⟩ := ChunkItem.parseChunkLoop_roundtrip sl.val
  rw [h_loop_eq]

  simp [ChunkItem.serialize_length]

theorem SizedList.reconstruct {α lenTyp : Type}
    [GetByteSize α] [Codec α] [LawfulCodec α] [ChunkItem α]
    [Coe lenTyp Nat] [Codec lenTyp] [LawfulCodec lenTyp]
    {sl : SizedList α lenTyp} {input rest : List UInt8} :
    SizedList.parser.run input = some (sl, rest) →
    input = SizedList.serialize sl ++ rest := by

  simp only [SizedList.parser, SizedList.serialize]
  intro h

  step_parser h → lenVal rest1 h_lenVal
  step_parser h → chunkVal rest2 h_chunkVal
  step_parser h → loopVal rest3 h_loopVal
  finish_parser h → h_sl

  finish_parser h_loopVal → h_match
  obtain ⟨items, h_loop_len⟩ := loopVal

  have h_rec_len   := LawfulCodec.reconstruct h_lenVal
  have h_rec_chunk := Parser.bytesWithProof_reconstruct h_chunkVal
  have h_rec_loop  :=
    ChunkItem.parseChunkLoop_reconstruct h_loop_len h_match

  rw [h_rec_len, h_rec_chunk, h_rec_loop]
  rw [h_sl]

  simp [List.append_assoc]
