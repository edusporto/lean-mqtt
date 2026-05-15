import LeanMqtt.Primitives.Proofs
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

theorem Property.roundtrip (p : Property) (rest : List UInt8) :
  Property.parser.run (p.serialize ++ rest) = some (p, rest) := by
  simp [Property.parser, Property.serialize]
  simp [Option.bind, Option.map]
  simp [VarInt.roundtrip]
  simp [Property.roundtrip_kind]

theorem Property.parser_reconstruct (input : List UInt8) (p : Property) (rest : List UInt8) :
  Property.parser.run input = some (p, rest) → input = p.serialize ++ rest := by
  sorry

theorem Property.parser_len_consumed (input : List UInt8) (p : Property) (rest : List UInt8) :
  Property.parser.run input = some (p, rest) → input.length = p.byteSize + rest.length := by
  intro h
  have h_eq := Property.parser_reconstruct _ _ _ h
  calc
    input.length = (p.serialize ++ rest).length     := by rw [h_eq]
    _            = p.serialize.length + rest.length := by rw [List.length_append]
    _            = p.byteSize + rest.length := rfl

theorem Property.byteSize_pos (p : Property) : 0 < p.byteSize := by
  -- Since p.serialize = p.id.serialize ++ ..., it must be at least
  -- the length of the serialized VarInt, which is strictly > 0.
  sorry
