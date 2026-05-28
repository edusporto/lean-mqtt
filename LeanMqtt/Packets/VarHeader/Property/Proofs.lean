import LeanMqtt.Primitives.UInt.Proofs
import LeanMqtt.Primitives.VarInt.Proofs
import LeanMqtt.Primitives.Str.Proofs
import LeanMqtt.Primitives.SizedList.Basic
import LeanMqtt.Helpers.ParserTactics
import LeanMqtt.Packets.VarHeader.Property.Basic

namespace Mqtt
open Mqtt

def Property.roundtrip_kind {k : Kind} (val : Property.typeOfKind k) {rest : List UInt8} :
    (Property.parserKind k).run (Property.serializeKind k val ++ rest) = some (val, rest) := by
  simp [Property.parserKind, Property.serializeKind]
  split
  repeat' simp only
  · simp only [UInt8.roundtrip]
  · simp only [UInt16.roundtrip]
  · simp only [UInt32.roundtrip]
  · simp only [VarInt.roundtrip]
  · simp only [BinaryData.roundtrip]
  · simp only [Str.roundtrip]
  · simp only [StrPair.roundtrip]
  · contradiction

theorem Property.reconstruct_kind {k : Property.Kind}
    {val : Property.typeOfKind k} {input rest : List UInt8} :
    (Property.parserKind k).run input = some (val, rest) →
    input = Property.serializeKind k val ++ rest := by
  cases k <;> simp only [Property.parserKind, Property.serializeKind]
  · exact UInt8.reconstruct
  · exact UInt16.reconstruct
  · exact UInt32.reconstruct
  · exact VarInt.reconstruct
  · exact BinaryData.reconstruct
  · exact Str.reconstruct
  · exact StrPair.reconstruct
  · intro h; contradiction

theorem Property.roundtrip (p : Property) {rest : List UInt8} :
    Property.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp [Property.parser, Property.serialize]
  simp [Option.bind, Option.map]
  simp [VarInt.roundtrip]
  simp [Property.roundtrip_kind]

theorem Property.reconstruct {p : Property} {input rest : List UInt8} :
    Property.parser.run input = some (p, rest) → input = p.serialize ++ rest := by

  simp only [Property.parser, Property.serialize]
  intro h

  step_parser h → idVal rest1 h_idVal
  step_parser h → valVal rest2 h_valVal
  finish_parser h → h_p

  have h_rec_id := VarInt.reconstruct h_idVal
  have h_rec_val := Property.reconstruct_kind h_valVal

  rw [h_rec_id, h_rec_val, h_p]
  simp [List.append_assoc]

theorem Property.parser_len_consumed {p : Property} {input rest : List UInt8} :
    Property.parser.run input = some (p, rest) → input.length = p.byteSize + rest.length := by
  intro h
  have h_eq := Property.reconstruct h
  simp [h_eq, List.length_append]

theorem Property.byteSize_pos (p : Property) : 0 < p.byteSize := by
  -- We always encode the id as a `VarInt`, so the byte size of a
  -- property must always be over 0
  simp [Property.byteSize, Property.serialize]
  unfold VarInt.serialize
  grind

instance : LawfulCodec Property where
  roundtrip   := Property.roundtrip
  reconstruct := Property.reconstruct

instance : ChunkItem Property where
  h_pos      := Property.byteSize_pos
  h_consumed := Property.parser_len_consumed
