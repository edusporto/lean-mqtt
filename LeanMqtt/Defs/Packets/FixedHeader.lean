import LeanMqtt.Defs.Primitives

namespace Mqtt

inductive WhichPkt where
  | connect
  | connack
  | publish
  | puback
  | pubrec
  | pubrel
  | pubcomp
  | subscribe
  | suback
  | unsubscribe
  | unsuback
  | pingreq
  | pingresp
  | disconnect
  | auth
deriving Repr, BEq

instance : Inhabited WhichPkt where
  default := .pingreq

structure PublishFlags where
  dup : BitVec 1
  qos : BitVec 2
  retain : BitVec 1

def WhichPkt.flagType : WhichPkt → Type
  | .connect     => { i : BitVec 4 // i = 0b0000 }
  | .connack     => { i : BitVec 4 // i = 0b0000 }
  | .publish     => PublishFlags
  | .puback      => { i : BitVec 4 // i = 0b0000 }
  | .pubrec      => { i : BitVec 4 // i = 0b0000 }
  | .pubrel      => { i : BitVec 4 // i = 0b0010 }
  | .pubcomp     => { i : BitVec 4 // i = 0b0000 }
  | .subscribe   => { i : BitVec 4 // i = 0b0010 }
  | .suback      => { i : BitVec 4 // i = 0b0000 }
  | .unsubscribe => { i : BitVec 4 // i = 0b0010 }
  | .unsuback    => { i : BitVec 4 // i = 0b0000 }
  | .pingreq     => { i : BitVec 4 // i = 0b0000 }
  | .pingresp    => { i : BitVec 4 // i = 0b0000 }
  | .disconnect  => { i : BitVec 4 // i = 0b0000 }
  | .auth        => { i : BitVec 4 // i = 0b0000 }

structure FixedHeader where
  which : WhichPkt
  flags : WhichPkt.flagType which
  size  : VarInt -- TODO: depend on information after

end Mqtt
