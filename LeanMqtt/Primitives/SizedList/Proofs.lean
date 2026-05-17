import LeanMqtt.Helpers.Proofs
import LeanMqtt.Helpers.NatifyUInt8
import LeanMqtt.Helpers.CrushLits

import LeanMqtt.Core.Parser.Proofs
import LeanMqtt.Primitives.Basic
import LeanMqtt.Primitives.SizedList.Basic

namespace Mqtt
open Mqtt

theorem ChunkItem.serialize_length {α : Type} [GetByteSize α] [ChunkItem α] (a : α) :
  (ChunkItem.serialize a).length = GetByteSize.byteSize a := by
  have h_rt := ChunkItem.roundtrip a []
  have h_c := ChunkItem.h_consumed (ChunkItem.serialize a ++ []) a [] h_rt
  simp at h_c
  exact h_c

theorem ChunkItem.serialize_list_length {α : Type}
  [GetByteSize α] [ChunkItem α] (l : List α) :
  (l.flatMap ChunkItem.serialize).length = List.rawByteSize l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append]
    rw [ChunkItem.serialize_length a]
    rw [ih]
    rfl

theorem ChunkItem.serialize_not_empty {α : Type}
  [GetByteSize α] [ChunkItem α] (a : α) (rest : List UInt8) :
  (ChunkItem.serialize a ++ rest).isEmpty = false := by
  cases h : ChunkItem.serialize a ++ rest with
  | nil =>
    have h_len : (ChunkItem.serialize a ++ rest).length = 0 := by rw [h]; rfl
    have h_pos := ChunkItem.h_pos a
    have h_a_len := ChunkItem.serialize_length a
    rw [List.length_append, h_a_len] at h_len
    omega
  | cons _ _ => rfl

theorem ChunkItem.parseChunkLoop_roundtrip {α : Type}
  [s : GetByteSize α] [c : ChunkItem α] (l : List α) :
  ∃ h, ChunkItem.parseChunkLoop (l.flatMap ChunkItem.serialize) = some ⟨l, h⟩ := by
  induction l with
  | nil =>
    simp [List.flatMap_nil]
    unfold ChunkItem.parseChunkLoop
    simp
  | cons a as ih =>
    have h_input :
        (a :: as).flatMap ChunkItem.serialize
      = ChunkItem.serialize a ++ as.flatMap ChunkItem.serialize := rfl
    rw [h_input]

    unfold ChunkItem.parseChunkLoop

    have h_not_empty := ChunkItem.serialize_not_empty a (as.flatMap ChunkItem.serialize)
    simp [h_not_empty]

    have h_rt := ChunkItem.roundtrip a (as.flatMap ChunkItem.serialize)

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

theorem SizedList.roundtrip {α lenTyp : Type}
  [GetByteSize α] [Coe lenTyp Nat] [ChunkItem α] [Codec lenTyp]
  (sl : SizedList α lenTyp) (rest : List UInt8) :
  SizedList.parser.run (SizedList.serialize sl ++ rest) = some (sl, rest) := by

  simp [SizedList.parser, SizedList.serialize, Option.bind]

  rw [Codec.roundtrip sl.len.val _]
  simp

  have h_len_eq : (sl.len.val : Nat) = (sl.val.flatMap ChunkItem.serialize).length := by
    rw [ChunkItem.serialize_list_length]
    exact sl.len_eq

  -- Bypass dependent type shenanigans on the byte parser
  have h_simple := roundtrip_bytes (sl.val.flatMap ChunkItem.serialize) rest
  rw [←h_len_eq] at h_simple
  have ⟨_, h_dep⟩ := bytesParserWithProof_eq_parser_success _ _ _ _ h_simple

  rw [h_dep]
  simp

  have ⟨h_loop_proof, h_loop_eq⟩ := ChunkItem.parseChunkLoop_roundtrip sl.val
  rw [h_loop_eq]

  simp
