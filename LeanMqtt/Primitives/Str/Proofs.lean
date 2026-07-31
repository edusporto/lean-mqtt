import LeanMqtt.Helpers.Proofs
import LeanMqtt.Helpers.ParserTactics
import LeanMqtt.Core.Parser.Proofs
import LeanMqtt.Primitives.Str.Basic
import LeanMqtt.Primitives.UInt.Proofs

namespace Mqtt
open Mqtt

theorem String.serialize_len (s : String) :
    s.serialize.length = s.utf8ByteSize := by
  rw [String.utf8ByteSize_ofByteArray]
  simp [String.serialize, String.toUTF8_eq_toByteArray]
  rw [Helpers.bytearray_tolist_eq_data_tolist]
  unfold String.utf8ByteSize
  exact @Array.size_eq_length_toList UInt8 s.toByteArray.data

theorem String.parser_len {len : Nat} {s : String} {inp rest : List UInt8} :
    (String.parser len).run inp = some (s, rest) → s.utf8ByteSize = len := by
  simp [String.parser]
  simp [Option.bind]
  intro h
  split at h
  · contradiction
  · next bytes h_parse =>
    simp only at h
    split at h
    · next h_valid =>
      simp at h
      have h_len := Parser.bytes_len h_parse
      rw [←h.1]
      simp only [String.fromUTF8, String.utf8ByteSize_ofByteArray, List.size_toByteArray]
      exact h_len
    · contradiction

theorem String.roundtrip (s : String) {rest : List UInt8} :
    (String.parser s.serialize.length).run (s.serialize ++ rest) = some (s, rest) := by
  simp only [String.serialize, String.parser]
  simp [String.toUTF8_eq_toByteArray, Option.bind]
  rw [Parser.bytes_roundtrip]
  simp
  split
  · next h =>
    simp [String.fromUTF8, Helpers.bytearray_list_roundtrip]
  · next h =>
    simp [Helpers.bytearray_list_roundtrip] at h
    exact absurd s.isValidUTF8 h

theorem String.roundtrip_proof (s : String) {rest : List UInt8} :
    (String.parserWithProof s.serialize.length).run (s.serialize ++ rest) =
    some (⟨s, s.serialize_len.symm⟩, rest) := by
  simp [String.parserWithProof]
  simp [Option.bind]
  split
  · next x val h_eq =>
    rw [Parser.bytesWithProof_roundtrip _ _] at h_eq
    contradiction
  · next val h_eq =>
    rw [Parser.bytesWithProof_roundtrip _ _] at h_eq
    simp only
    injection h_eq with h_eq
    split
    · next h_utf8 =>
      simp
      subst h_eq
      simp only [and_true]
      congr
      apply Helpers.bytearray_list_roundtrip
    · next h_wrong =>
      rw [←h_eq] at h_wrong
      simp [String.serialize, Helpers.bytearray_list_roundtrip] at h_wrong
      exact absurd s.isValidUTF8 h_wrong

theorem String.reconstructWithProof {len : Nat} {s : { s : String // s.utf8ByteSize = len }}
    {input rest : List UInt8} :
    (String.parserWithProof len).run input = some (s, rest) → input = s.val.serialize ++ rest := by

  simp only [String.parserWithProof, String.serialize]
  intro h
  step_parser h → bytesVal rest1 h_bytesVal

  split at h
  · next h_valid =>
    finish_parser h → h_result

    have h_rec := Parser.bytesWithProof_reconstruct h_bytesVal
    rw [h_rec, h_result]

    simp [String.fromUTF8, String.toUTF8_eq_toByteArray, Helpers.list_bytearray_roundtrip]
  · contradiction

theorem String.parserWithProof_eq_parser_success {n : Nat} {s : String}
    {inp rest : List UInt8} :
    (String.parser n).run inp = some (s, rest) →
    ∃ h, (String.parserWithProof n).run inp = some (⟨s, h⟩, rest) := by
  intro h_simple
  have h_parser_len := String.parser_len h_simple

  -- Unfold both parsers
  simp only [String.parser, String.parserWithProof] at *
  simp only [StateT.run_bind, Option.bind_eq_bind, Option.bind] at *

  -- Step through the simple parser to extract facts
  split at h_simple
  · contradiction -- bytesParser failed
  · next bytes h_bytes =>
    simp only at h_simple
    split at h_simple
    · next h_utf8 =>
      -- If simple parser succeeded, bytesParserWithProof must succeed too
      -- We construct the proof needed for the dependent parser
      simp at h_simple
      have ⟨h_len, h_parsed⟩ := Parser.bytes_imp_bytesWithProof h_bytes
      rw [h_parsed]
      simp [h_utf8]
      repeat' constructor
      · exact h_simple.left
      · exact h_parser_len
      · exact h_simple.right
    · contradiction

theorem Str.roundtrip (s : Str) (rest : List UInt8) :
    Str.parser.run (s.serialize ++ rest) = some (s, rest) := by
  simp [Str.parser, Str.serialize]

  simp [UInt16.roundtrip s.len.val, Option.map]

  /-
    To use the String.roundtrip theorem, we need to substitute `s.len.val.toNat`
    with `s.val.serialize.length`. However, due to dependent type shenanigans,
    we can't do this substitution in `String.parserWithProof`. So, we do the
    substitution in the simple parser (`String.parser`), then use the projection
    lemma (`String.parserWithProof_eq_parser_success`) to show it also holds for
    `String.parserWithProof`.
  -/
  have h_simple := @String.roundtrip s.val rest

  have h_len_eq : s.len.val.toNat = s.val.serialize.length := by
    rw [String.serialize_len]
    exact s.len.property.symm
  rw [←h_len_eq] at h_simple

  have ⟨_, h_dep⟩ := String.parserWithProof_eq_parser_success h_simple

  rw [h_dep]

theorem Str.reconstruct {s : Str} {input rest : List UInt8} :
    Str.parser.run input = some (s, rest) → input = s.serialize ++ rest := by

  simp only [Str.parser, Str.serialize]
  intro h

  step_parser h → lenVal rest1 h_lenVal
  step_parser h → strVal rest2 h_strVal
  finish_parser h → h_result

  rw [UInt16.reconstruct h_lenVal, String.reconstructWithProof h_strVal, h_result]
  simp [List.append_assoc]

theorem StrPair.roundtrip (p : StrPair) {rest : List UInt8} :
    StrPair.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp [StrPair.parser, StrPair.serialize, Option.bind, Option.map]
  simp only [Str.roundtrip _ _]

theorem StrPair.reconstruct {p : StrPair} {input rest : List UInt8} :
    StrPair.parser.run input = some (p, rest) → input = p.serialize ++ rest := by
  simp only [StrPair.parser, StrPair.serialize]
  intro h

  step_parser h → s1Val rest1 h_s1Val
  step_parser h → s2Val rest2 h_s2Val
  finish_parser h → h_result

  subst h_result

  rw [Str.reconstruct h_s1Val, Str.reconstruct h_s2Val]
  simp [List.append_assoc]

theorem BinaryData.roundtrip (b : BinaryData) {rest : List UInt8} :
    BinaryData.parser.run (b.serialize ++ rest) = some (b, rest) := by
  simp only [BinaryData.parser, BinaryData.serialize]
  simp [Option.bind, Option.map]

  rw [UInt16.roundtrip]
  simp only

  have h_len_eq : b.len.val.toNat = b.val.toList.length := by
    simp only [Array.length_toList]
    exact b.len.property.symm

  /-
    Due to dependent type shenanigans, we can't rewrite the current goal
    with `h_len_eq`. So, we rewrite it in the simpler parser, and prove
    that it implies our current goal. See `Str.roundtrip` for more.
  -/
  have h_simple := Parser.bytes_roundtrip b.val.toList rest
  rw [←h_len_eq] at h_simple
  have ⟨_, h_dep⟩ := Parser.bytes_imp_bytesWithProof h_simple

  rw [h_dep]

theorem BinaryData.reconstruct {b : BinaryData} {input rest : List UInt8} :
    BinaryData.parser.run input = some (b, rest) → input = b.serialize ++ rest := by

  simp only [BinaryData.parser, BinaryData.serialize]
  intro h

  step_parser h → lenVal rest1 h_lenVal
  step_parser h → bytesVal rest2 h_bytesVal
  finish_parser h → h_result

  rw [UInt16.reconstruct h_lenVal,
      Parser.bytesWithProof_reconstruct h_bytesVal,
      h_result]
  simp [List.append_assoc]

instance : LawfulCodec Str where
  roundtrip := Str.roundtrip
  reconstruct := Str.reconstruct

instance : LawfulCodec StrPair where
  roundtrip := StrPair.roundtrip
  reconstruct := StrPair.reconstruct

instance : LawfulCodec BinaryData where
  roundtrip := BinaryData.roundtrip
  reconstruct := BinaryData.reconstruct

theorem Str.serialize_len (s : Str) : s.serialize.length = GetByteSize.byteSize s := by
  simp [Str.serialize, GetByteSize.byteSize, List.length_append]
  rw [UInt16.parser_len, String.serialize_len]
  have h := s.len.property
  simp [GetByteSize.byteSize] at h
  omega

theorem StrPair.serialize_len (p : StrPair) : p.serialize.length = GetByteSize.byteSize p := by
  change (p.1.serialize ++ p.2.serialize).length = GetByteSize.byteSize p.1 + GetByteSize.byteSize p.2
  rw [List.length_append, Str.serialize_len, Str.serialize_len]

theorem BinaryData.serialize_len (b : BinaryData) : b.serialize.length = GetByteSize.byteSize b := by
  simp [BinaryData.serialize, GetByteSize.byteSize, List.length_append]
  rw [UInt16.parser_len]
  have h := b.len.property
  simp [GetByteSize.byteSize] at h
  omega

instance : LawfulByteSize Str where
  serialize_len := Str.serialize_len

instance : LawfulByteSize StrPair where
  serialize_len := StrPair.serialize_len

instance : LawfulByteSize BinaryData where
  serialize_len := BinaryData.serialize_len

end Mqtt
