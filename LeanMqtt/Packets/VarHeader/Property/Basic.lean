import LeanMqtt.Core.WithByteSize
import LeanMqtt.Core.Codec
import LeanMqtt.Primitives.UInt.Basic
import LeanMqtt.Primitives.VarInt.Basic
import LeanMqtt.Primitives.Str.Basic

namespace Mqtt
open Mqtt

/-!
# Properties

This module defines the MQTT `Property` structure, which encodes optional
metadata in Variable Headers. It uses a three-layer dependent typing approach
(`ID -> Kind -> Type`) to automatically resolve the specific Lean type of a
property value based on its identifier.
-/

/- ========================================================================= -/
/-! ## Property Structure -/

/--
Defines the type of the value stored in a property.

We do a three layer approach (ID -> Kind -> Type) instead of deriving
types directly from the ID to help Lean automatically decide the type of
each property in `Property.serializeKind`, without having to include
proofs in each branch.
-/
-- TODO: some properties actually change their behavior according to the specific
-- id they represent. We plan on dealing with this when we tackle MQTT Payloads
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

def Property.byteSizeKind (k : Property.Kind) (val : Property.typeOfKind k) : Nat :=
  match k with
  | .u8     => val.byteSize
  | .u16    => val.byteSize
  | .u32    => val.byteSize
  | .varInt => val.byteSize
  | .binary => val.byteSize
  | .string => val.byteSize
  | .pair   => val.byteSize
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

abbrev Property.valType (id : VarInt) : Type :=
  Property.typeOfKind (getKind id)

/--
A dependently-typed structure representing an MQTT Property. The specific type
of `val` is dynamically determined by the `id` field.
-/
structure Property where
  id  : VarInt
  val : Property.valType id

def Property.serialize (p : Property) : List UInt8 :=
  p.id.serialize ++ Property.serializeKind (getKind p.id) p.val

def Property.parser : Parser Property := do
  let id ← VarInt.parser
  let kind := Property.getKind id
  let val ← Property.parserKind kind
  return { id, val }

@[simp]
def Property.byteSize (p : Property) : Nat :=
  p.id.byteSize + Property.byteSizeKind (Property.getKind p.id) p.val

instance : GetByteSize Property where
  byteSize := Property.byteSize

instance : Codec Property where
  parser      := Property.parser
  serialize   := Property.serialize
