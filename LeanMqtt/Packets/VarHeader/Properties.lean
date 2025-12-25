import LeanMqtt.Primitives.Basic

namespace Mqtt
open Mqtt

/- ========================= Property ========================= -/

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

abbrev Property.valType (id : VarInt) : Type :=
  Property.typeOfKind (getKind id)

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
  p.serialize.length

/- ========================= Properties ========================= -/

instance : GetLength (List Property) where
  length l := l.foldl (fun acc p => acc + (Property.serialize p).length) 0 -- Placeholder, will be fixed

abbrev Properties := WithLength (List Property) VarInt

def Properties.serialize (ps : Properties) : List UInt8 :=
  VarInt.serialize ps.len ++
  ps.val.foldl (fun acc p => acc ++ p.serialize) []

def parsePropsLoop (input : List UInt8) : Option (List Property) :=
  if /-h_empty :-/ input.isEmpty then
    some []
  else
    -- Run the parser manually on the current list
    match Property.parser.run input with
    | some (p, rest) =>
      -- CRITICAL: We explicitly check that the parser consumed at least 1 byte.
      -- This guarantees 'rest' is strictly smaller than 'input'.
      -- TODO: we may be able to derive this check instead performing it
      if /-h_progress :-/ rest.length < input.length then
        match parsePropsLoop rest with
        | some tail => some (p :: tail)
        | none      => none
      else
        -- Parser succeeded but consumed 0 bytes (infinite loop risk).
        -- Treat as an error.
        none
    | none => none
termination_by input.length

def Properties.parser : Parser Properties := do
  -- 1. Parse the Length Prefix
  let len ← VarInt.parser
  let ⟨chunk, h_chunk_len⟩ ← bytesParserWithProof len

  match h_parsed : parsePropsLoop chunk with
  | some props =>
    have h_len : len.val = (props.foldl (fun acc p => acc + p.byteSize) 0) := by
      -- This proof will need to be fixed.
      sorry

    return { val := props, len := ⟨len, sorry⟩ }
  | none => none

end Mqtt
