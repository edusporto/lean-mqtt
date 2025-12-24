import LeanMqtt.Core.WithLength

instance : Coe UInt16 Nat where
  coe := UInt16.toNat
instance : Coe UInt32 Nat where
  coe := UInt32.toNat

namespace Mqtt

abbrev Str := WithLength String UInt16

abbrev StrPair := Str × Str

abbrev BinaryData := WithLength (Array UInt8) UInt16

/--
  The maximum value for a
  [Variable Byte Integer](https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901011)
  is 268_435_455 (128^4 - 1).
-/
abbrev VarInt.limit : Nat := 268_435_456

/--
  Type representing a
  [Variable Byte Integer](https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901011).
-/
abbrev VarInt := Fin VarInt.limit

instance : Coe VarInt Nat where
  coe v := v.toNat

end Mqtt
