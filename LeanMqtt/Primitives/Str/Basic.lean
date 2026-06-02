import LeanMqtt.Primitives.UInt.Basic
import LeanMqtt.Core.Codec

namespace Mqtt

/- ========================= String ========================= -/

-- TODO: benchmark if `ByteArray.toList arr` is faster than `Array.toList arr.data`
def String.serialize (s : String) := s.toUTF8.toList

def String.parser (len : Nat) : Parser String := do
  let bytes ← Parser.bytes len
  let txt := bytes.toByteArray
  if h_valid : txt.IsValidUTF8
    then some (String.fromUTF8 txt h_valid)
    else none

def String.parserWithProof (n : Nat) : Parser { s : String // s.utf8ByteSize = n } := do
  let ⟨bytes, h_len⟩ ← Parser.bytesWithProof n
  let txt := bytes.toByteArray
  if h_valid : txt.IsValidUTF8 then
    let s := String.fromUTF8 txt h_valid

    have h_size : s.utf8ByteSize = n := by
      simp only [String.utf8ByteSize]
      simp only [s, String.fromUTF8, txt, List.size_toByteArray]
      exact h_len

    return ⟨s, h_size⟩
  else
    none

/- ========================= Str ========================= -/

abbrev Str := WithByteSize String UInt16

def Str.serialize (s : Str) : List UInt8 :=
  UInt16.serialize (s.len) ++ String.serialize s.val

def Str.parser : Parser Str := do
  let len ← UInt16.parser
  let ⟨str, h⟩ ← String.parserWithProof len.toNat
  return { val := str, len := ⟨len, h⟩ }

instance : Codec Str where
  parser := Str.parser
  serialize := Str.serialize

/- ========================= StrPair ========================= -/

abbrev StrPair := Str × Str

def StrPair.serialize (p : StrPair) : List UInt8 :=
  Str.serialize (p.fst) ++ Str.serialize (p.snd)

def StrPair.parser : Parser StrPair := do
  let s1 ← Str.parser
  let s2 ← Str.parser
  return ⟨s1, s2⟩

instance : Codec StrPair where
  parser := StrPair.parser
  serialize := StrPair.serialize

/- ========================= BinaryData ========================= -/

abbrev BinaryData := WithByteSize (Array UInt8) UInt16

def BinaryData.serialize (b : BinaryData) :=
  UInt16.serialize (b.len) ++ b.val.toList

def BinaryData.parser : Parser BinaryData := do
  let len ← UInt16.parser
  let ⟨l, h⟩ ← Parser.bytesWithProof len.toNat
  let b := l.toArray
  return { val := b, len := ⟨len, h⟩ }

instance : Codec BinaryData where
  parser := BinaryData.parser
  serialize := BinaryData.serialize

end Mqtt
