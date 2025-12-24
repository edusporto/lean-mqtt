import LeanMqtt.Serialization.Packets.Properties
import LeanMqtt.Proofs.Primitives
import LeanMqtt.Proofs.Packets.Property

namespace Mqtt

-- TODO: prove
theorem parsePropsLoop_len (chunk : List UInt8) (l : List Property) :
  parsePropsLoop chunk = some l → chunk.length = (l.foldl (fun acc p => acc + p.byteSize) 0) := by
  -- simp [GetLength.length]
  sorry

theorem Properties.roundtrip (ps : Properties) (rest : List UInt8) :
  Properties.parser.run (ps.serialize ++ rest) = some (ps, rest) := by
  sorry

end Mqtt
