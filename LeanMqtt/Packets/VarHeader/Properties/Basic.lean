import LeanMqtt.Primitives.Basic
import LeanMqtt.Packets.VarHeader.Property.Basic
import LeanMqtt.Packets.VarHeader.Property.Proofs

namespace Mqtt
open Mqtt

/- ========================= Properties ========================= -/

abbrev Properties.rawByteSize (l : List Property) : Nat
  := (l.map Property.byteSize).sum

instance : GetByteSize (List Property) where
  byteSize := Properties.rawByteSize

abbrev Properties := WithByteSize (List Property) VarInt

def Properties.serialize (ps : Properties) : List UInt8 :=
  -- VarInt.serialize ps.len ++
  -- ps.val.foldl (fun acc p => acc ++ p.serialize) []
  VarInt.serialize ps.len ++ ps.val.flatMap Property.serialize

def parsePropsLoop (input : List UInt8) :
  Option { ps : (List Property) // input.length = Properties.rawByteSize ps } :=
  if h_empty : input.isEmpty then
    some ⟨[], by
      have h_len_zero : input.length = 0 := by grind
      simp [h_len_zero, Properties.rawByteSize]
    ⟩
  else
    match h_parse : Property.parser.run input with
    | some (p, rest) =>
      match parsePropsLoop rest with
      | some ⟨tail, h_tail_len⟩ =>
        let h_len_ps : input.length = Properties.rawByteSize (p :: tail) := by
          have h_consumed : input.length = p.byteSize + rest.length
            := Property.parser_len_consumed input p rest h_parse
          rw [h_tail_len] at h_consumed
          exact h_consumed

        some ⟨(p :: tail), h_len_ps⟩
      | none => none
    | none => none
termination_by input.length
decreasing_by
  have h_consumed := Property.parser_len_consumed input p rest h_parse
  have h_pos := Property.byteSize_pos p
  omega

def Properties.parser : Parser Properties := do
  let len ← VarInt.parser
  let ⟨chunk, h_chunk_len⟩ ← bytesParserWithProof len

  match parsePropsLoop chunk with
  | some ⟨props, h_loop_len⟩ =>
    have h_len : len.val = (props.map Property.byteSize).sum := by
      rw [← h_chunk_len]
      exact h_loop_len

    return { val := props, len := ⟨len, h_len⟩ }
  | none => none

end Mqtt
