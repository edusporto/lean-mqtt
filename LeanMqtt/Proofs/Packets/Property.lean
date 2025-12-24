import LeanMqtt.Serialization.Packets.Property
import LeanMqtt.Proofs.Primitives

namespace Mqtt

def Property.roundtrip_kind (k : Property.Kind) (val : Property.typeOfKind k) (rest : List UInt8) :
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

end Mqtt
