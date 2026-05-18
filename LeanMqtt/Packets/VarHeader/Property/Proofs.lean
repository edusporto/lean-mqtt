import LeanMqtt.Primitives.Proofs
import LeanMqtt.Primitives.SizedList.Basic
import LeanMqtt.Packets.VarHeader.Property.Basic

namespace Mqtt
open Mqtt

def Property.roundtrip_kind (k : Kind) (val : Property.typeOfKind k) (rest : List UInt8) :
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

theorem Property.reconstruct_kind (k : Property.Kind) (input : List UInt8)
  (val : Property.typeOfKind k) (rest : List UInt8) :
  (Property.parserKind k).run input = some (val, rest) → input = Property.serializeKind k val ++ rest := by
  cases k <;> simp only [Property.parserKind, Property.serializeKind]
  · exact UInt8.reconstruct input val rest
  · exact UInt16.reconstruct input val rest
  · exact UInt32.reconstruct input val rest
  · exact VarInt.reconstruct input val rest
  · exact BinaryData.reconstruct input val rest
  · exact Str.reconstruct input val rest
  · exact StrPair.reconstruct input val rest
  · intro h; contradiction

theorem Property.roundtrip (p : Property) (rest : List UInt8) :
  Property.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp [Property.parser, Property.serialize]
  simp [Option.bind, Option.map]
  simp [VarInt.roundtrip]
  simp [Property.roundtrip_kind]

theorem Property.reconstruct (input : List UInt8) (p : Property) (rest : List UInt8) :
  Property.parser.run input = some (p, rest) → input = p.serialize ++ rest := by

  simp only [Property.parser, Property.serialize]
  intro h

  obtain ⟨id, mid, h_id, h_next⟩ := Parser.bind_run_success _ _ _ _ _ h
  obtain ⟨val, mid2, h_val, h_next2⟩ := Parser.bind_run_success _ _ _ _ _ h_next
  obtain ⟨h_p, h_rest⟩ := Parser.pure_run_success _ _ _ _ h_next2

  subst h_rest
  have h_rec_id := VarInt.reconstruct _ _ _ h_id
  have h_rec_val := Property.reconstruct_kind (getKind id) _ _ _ h_val

  rw [h_rec_id, h_rec_val, h_p]
  simp [List.append_assoc]

theorem Property.parser_len_consumed (input : List UInt8) (p : Property) (rest : List UInt8) :
  Property.parser.run input = some (p, rest) → input.length = p.byteSize + rest.length := by
  intro h
  have h_eq := Property.reconstruct _ _ _ h
  simp [h_eq, List.length_append]

theorem Property.byteSize_pos (p : Property) : 0 < p.byteSize := by
  -- We always encode the id as a `VarInt`, so the byte size of a
  -- property must always be over 0
  simp [Property.byteSize, Property.serialize]
  unfold VarInt.serialize
  grind

instance : ChunkItem Property where
  parser      := Property.parser
  serialize   := Property.serialize
  h_pos       := Property.byteSize_pos
  h_consumed  := Property.parser_len_consumed
  roundtrip   := Property.roundtrip
  reconstruct := Property.reconstruct
