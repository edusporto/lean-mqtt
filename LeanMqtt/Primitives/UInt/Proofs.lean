import Std.Tactic.BVDecide
import LeanMqtt.Helpers.Proofs
import LeanMqtt.Helpers.ParserTactics
import LeanMqtt.Core.Parser.Proofs
import LeanMqtt.Core.Codec
import LeanMqtt.Primitives.UInt.Basic

namespace Mqtt
open Mqtt

theorem UInt8.parser_len (n : UInt8) :
    n.serialize.length = 1 := by
  rfl

theorem UInt8.roundtrip (b : UInt8) {rest : List UInt8} :
    UInt8.parser.run (b.serialize ++ rest) = some (b, rest) := by
    simp [UInt8.parser, UInt8.serialize]

theorem UInt8.reconstruct {b : UInt8} {input rest : List UInt8} :
    UInt8.parser.run input = some (b, rest) → input = b.serialize ++ rest := by
  simp [UInt8.parser, UInt8.serialize, StateT.run_bind, StateT.run_get]
  split
  · intro h
    contradiction
  · intro h
    simp at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    rfl

theorem UInt16.parser_len (n : UInt16) :
    n.serialize.length = 2 := by
  rfl

theorem UInt16.roundtrip (n : UInt16) {rest : List UInt8} :
    UInt16.parser.run (n.serialize ++ rest) = some (n, rest) := by
  simp [UInt16.parser, UInt16.serialize, UInt8.parser]
  bv_decide

theorem UInt16.reconstruct {n : UInt16} {input rest : List UInt8} :
    UInt16.parser.run input = some (n, rest) → input = n.serialize ++ rest := by

  simp only [UInt16.parser, UInt16.serialize]
  intro h

  step_parser h → byte1 rest1 h_byte1
  step_parser h → byte2 rest2 h_byte2
  finish_parser h → h_result

  rw [UInt8.reconstruct h_byte1, UInt8.reconstruct h_byte2]
  simp [UInt8.serialize, List.cons_append, List.nil_append]
  bv_decide

instance : Codec UInt16 where
  parser      := UInt16.parser
  serialize   := UInt16.serialize
  roundtrip   := UInt16.roundtrip
  reconstruct := UInt16.reconstruct

theorem UInt32.parser_len (n : UInt32) :
    n.serialize.length = 4 := by
  rfl

theorem UInt32.roundtrip (n : UInt32) {rest : List UInt8} :
    UInt32.parser.run (n.serialize ++ rest) = some (n, rest) := by
  simp [UInt32.parser, UInt32.serialize, UInt8.parser, Option.bind, Option.map]
  bv_decide

theorem UInt32.reconstruct {n : UInt32} {input rest : List UInt8} :
    UInt32.parser.run input = some (n, rest) → input = n.serialize ++ rest := by

  simp only [UInt32.parser, UInt32.serialize]
  intro h

  step_parser h → byte1 rest1 h_byte1
  step_parser h → byte2 rest2 h_byte2
  step_parser h → byte3 rest3 h_byte3
  step_parser h → byte4 rest4 h_byte4
  finish_parser h → h_result

  rw [UInt8.reconstruct h_byte1,
      UInt8.reconstruct h_byte2,
      UInt8.reconstruct h_byte3,
      UInt8.reconstruct h_byte4]

  simp [UInt8.serialize, List.cons_append, List.nil_append]
  bv_decide

end Mqtt
