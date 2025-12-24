import LeanMqtt.Core.WithLength
import LeanMqtt.Serialization.Packets.Property

namespace Mqtt

instance : GetLength (List Property) where
  length l := l.foldl (fun acc p => acc + (Property.serialize p).length) 0 -- Placeholder, will be fixed

abbrev Properties := WithLength (List Property) VarInt

end Mqtt
