import LeanMqtt.Core.Parser
import LeanMqtt.Defs.Packets.Property
import LeanMqtt.Serialization.Primitives

namespace Mqtt
open Mqtt

/--
  Serializes the value stored in a property from its kind.

  We pass `k`, and `val` of type `Property.typeOfKind k` to help Lean automatically
  reduce the type of `val` to what's desired in each branch.
-/
def Property.serializeKind (k : Property.Kind) (val : Property.typeOfKind k) : List UInt8 :=
  match k with
  | .u8     => val.serialize
  | .u16    => val.serialize
  | .u32    => val.serialize
  | .varInt => val.serialize
  | .binary => val.serialize
  | .string => val.serialize
  | .pair   => val.serialize
  | .none   => nomatch val

def Property.parserKind (k : Property.Kind) : Parser (Property.typeOfKind k) :=
  match k with
  | .u8     => UInt8.parser
  | .u16    => UInt16.parser
  | .u32    => UInt32.parser
  | .varInt => VarInt.parser
  | .binary => BinaryData.parser
  | .string => Str.parser
  | .pair   => StrPair.parser
  | .none   => none

def Property.serialize (p : Property) : List UInt8 :=
  p.id.serialize ++ Property.serializeKind (getKind p.id) p.val

def Property.parser : Parser Property := do
  let id ← VarInt.parser
  let kind := Property.getKind id
  let val ← Property.parserKind kind
  return { id, val }

@[simp]
def Property.byteSize (p : Property) : Nat :=
  p.serialize.length

end Mqtt
