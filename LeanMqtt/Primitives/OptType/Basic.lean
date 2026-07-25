import LeanMqtt.Core.Codec

namespace Mqtt
open Mqtt

/-!
# Optional Types

This module provides the generic `OptType` primitive for fields that are conditionally
present in the binary payload based on a boolean condition (e.g., packet identifiers
that are only present when QoS > 0).
-/

/- ========================================================================= -/
/-! ## Conditional Presence (`OptType`) -/

/--
`OptType` is a generic primitive for conditionally present fields.
It evaluates definitionally to `α` when `b` is `true`, and `Unit` when `b` is `false`.

At first glance, using `Bool` instead of `Prop` might seem like it may wield incorrect
results, with a buggy parser breaking the protocol by always receiving a constant `false`.
The guarantee is preserved because the boolean is embedded directly into the type
signature of the parent structure.

For example, if we declare the following, in `Mqtt.Var_Publish`:
```lean
packet_id : OptType UInt16 (qos.val > 0)
```
Any parser or serializer that passes a different condition (e.g., `OptType UInt16 false`)
will yield a mismatched type. Lean's type checking will catch this mismatch and reject
the implementation.
-/
abbrev OptType (α : Type) (b : Bool) : Type :=
  cond b α Unit

def OptType.serialize {α : Type} [c : Codec α] (b : Bool) (v : OptType α b) : List UInt8 :=
  match b, v with
  | true,  val => @Codec.serialize α c val
  | false, _   => []

def OptType.parser {α : Type} [c : Codec α] (b : Bool) : Parser (OptType α b) :=
  match b with
  | true  => @Codec.parser α c
  | false => pure ()
