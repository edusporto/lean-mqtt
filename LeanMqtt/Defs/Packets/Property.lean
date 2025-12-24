import LeanMqtt.Defs.Primitives

namespace Mqtt

/--
  Defines the type of the value stored in a property.

  We do a three layer approach (ID -> Kind -> Type) instead of deriving
  types directly from the ID to help Lean automatically decide the type of
  each property in `Property.serializeKind`, without having to include
  proofs in each branch.
-/
inductive Property.Kind
  | u8 | u16 | u32 | varInt | binary | string | pair | none
  deriving DecidableEq

def Property.getKind (id : VarInt) : Property.Kind :=
  match id with
  |  1 | 23 | 25 | 36 | 37 | 40 | 41 | 42 => .u8
  | 19 | 33 | 34 | 35                     => .u16
  |  2 | 17 | 24 | 39                     => .u32
  | 11                                    => .varInt
  |  9 | 22                               => .binary
  |  3 |  8 | 18 | 21 | 26 | 28 | 31      => .string
  | 38                                    => .pair
  | _                                     => .none

abbrev Property.typeOfKind (k : Property.Kind) : Type :=
  match k with
  | .u8     => UInt8
  | .u16    => UInt16
  | .u32    => UInt32
  | .varInt => VarInt
  | .binary => BinaryData
  | .string => Str
  | .pair   => StrPair
  | .none   => Empty

abbrev Property.valType (id : VarInt) : Type :=
  Property.typeOfKind (getKind id)

structure Property where
  id  : VarInt
  val : Property.valType id

end Mqtt
