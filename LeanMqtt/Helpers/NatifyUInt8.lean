import Lean

open Lean Meta Elab Tactic

/-!
# UInt8 Natification Tactics

This module provides tactics and lemmas for reasoning about `UInt8`
by mapping them to `Nat`. This simplifies the visual goal state, making
it easier to construct manual proofs or to prepare hypotheses for solvers.
-/

/--
Proves that two `UInt8` values are equal if and only if their `toNat` representations are equal.
Useful for rewriting `UInt8` equalities into `Nat` equalities.

This could also be done with `UInt8.toNat_inj`, but this theorem works better to remove
`UInt8` from hypotheses and goals.
-/
theorem natify_uint8_eq_iff (a b : UInt8) : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, fun h => by
    cases a
    cases b
    congr
    exact BitVec.eq_of_toNat_eq h⟩

/--
Proves an upper bound of 256 for `UInt8`s transformed into `Nat`s.
Provided for manual application or for passing to solvers like `grind`.
-/
theorem UInt8.toNat_lt_256 (b : UInt8) : b.toNat < 256 :=
  b.toBitVec.isLt

/--
Iterates through the local context. For every variable `x : UInt8`,
it adds a hypothesis `h_x_lt_256 : x.toNat < 256` using `UInt8.toNat_lt_size`,
unless a hypothesis with that exact name already exists.
-/
elab "inject_uint8_bounds" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut uint8Vars := #[]

  -- 1. Collect all UInt8 variables from the local context
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    if type.isConstOf ``UInt8 then
      uint8Vars := uint8Vars.push decl

  -- 2. Inject bounds for each, if not already present
  for decl in uint8Vars do
    -- Create a clean, predictable name for the new hypothesis
    let boundName := Name.mkSimple (s!"h_{decl.userName}_lt_256")

    -- Check if a hypothesis with this name already exists
    if !lctx.usesUserName boundName then
      let boundIdent := mkIdent boundName
      let varIdent := mkIdent decl.userName

      -- Execute the tactic to add the hypothesis
      let stx ← `(tactic| have $boundIdent := UInt8.toNat_lt_256 $varIdent)
      evalTactic stx

/--
A tactic that transforms `UInt8` goals and hypotheses into their `Nat` equivalents.
It simplifies standard `UInt8` operations to provide a cleaner goal state and
injects a proof `b.toNat < 256` for each `b : UInt8` in the hypotheses.

It is useful to run `simp at *` after `natify_uint8` for better cleanup.
-/
macro "natify_uint8" : tactic => `(tactic|
  (
    inject_uint8_bounds
    simp only [
      natify_uint8_eq_iff,
      UInt8.lt_iff_toNat_lt,
      UInt8.le_iff_toNat_le,
      UInt8.toNat_ofNat
    ] at *
  )
)
