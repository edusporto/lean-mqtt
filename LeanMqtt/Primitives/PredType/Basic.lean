import Lean
import LeanMqtt.Core.Codec

namespace Mqtt
open Mqtt

/-!
  `PredType` is a generic primitive for fields that are only correct when a
  given predicate is true.
-/
structure Condition where
  desc : String
  p : Prop
  dec : Decidable p

instance (c : Condition) : Decidable c.p := c.dec

abbrev AllHold {α : Type} (gen : α → List Condition) (v : α) : Prop :=
  ∀ c ∈ gen v, c.p

abbrev PredType (α : Type) (gen : α → List Condition) : Type :=
  { val : α // AllHold gen val }

theorem PredType.get_proof {α : Type} {gen : α → List Condition} (v : PredType α gen)
    (idx : Nat) (h_idx : idx < (gen v.val).length := by exact of_decide_eq_true rfl) :
    ((gen v.val).get ⟨idx, h_idx⟩).p :=
  v.property _ (List.get_mem ..)

def PredType.serialize {α : Type} [c : Codec α] {gen : α → List Condition} (v : PredType α gen) : List UInt8 :=
  @Codec.serialize α c v.val

def PredType.parser {α : Type} [c : Codec α] (gen : α → List Condition) : Parser (PredType α gen) := do
  let val ← @Codec.parser α c
  if h : AllHold gen val then
    return ⟨val, h⟩
  else
    failure

macro "ensure! " p:term : term =>
  let desc := Lean.Syntax.mkStrLit (toString p.raw)
  `( { desc := $desc, p := $p, dec := inferInstance } )

end Mqtt
