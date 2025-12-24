import LeanMqtt.Core.Parser
import LeanMqtt.Defs.Packets.Properties
import LeanMqtt.Serialization.Primitives

namespace Mqtt

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
