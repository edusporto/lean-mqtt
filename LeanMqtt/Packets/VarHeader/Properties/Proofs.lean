import LeanMqtt.Packets.VarHeader.Basic
import LeanMqtt.Packets.VarHeader.Property.Basic
import LeanMqtt.Packets.VarHeader.Property.Proofs
import LeanMqtt.Packets.VarHeader.Properties.Basic
import LeanMqtt.Packets.VarHeader.Variations
import LeanMqtt.Primitives.UInt.Proofs
import LeanMqtt.Primitives.VarInt.Proofs
import LeanMqtt.Primitives.SizedList.Proofs

namespace Mqtt
open Mqtt

theorem Properties.roundtrip (ps : Properties) {rest : List UInt8} :
    Properties.parser.run (ps.serialize ++ rest) = some (ps, rest) :=
  SizedList.roundtrip ps

theorem Properties.reconstruct
    {ps : Properties} {input rest : List UInt8} :
    Properties.parser.run input = some (ps, rest) →
    input = ps.serialize ++ rest :=
  SizedList.reconstruct
