import Lean

open Lean Meta Elab Tactic

--------------------------------------------------------------------------------
-- 1. Helper Lemmas
--------------------------------------------------------------------------------
theorem natify_uint8_eq_iff (a b : UInt8) : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => h ▸ rfl, fun h => by
    -- Unwrap UInt8 to expose the underlying BitVec 8
    cases a
    cases b
    congr
    -- Lean core contains the fundamental extensionality lemma for BitVec
    exact BitVec.eq_of_toNat_eq h⟩

--------------------------------------------------------------------------------
-- 2. MetaM Bounds Injector
--------------------------------------------------------------------------------
elab "inject_uint8_bounds" : tactic => do
  withMainContext do
    let lctx ← getLCtx
    let mut mvarId ← getMainGoal
    for decl in lctx do
      if decl.isImplementationDetail then continue

      if decl.type.isConstOf ``UInt8 then
        let x := decl.toExpr
        let boundName := Name.mkSimple (decl.userName.toString ++ "_bound")
        let type ← mkAppM ``LT.lt #[← mkAppM ``UInt8.toNat #[x], mkNatLit 256]

        let newGoal ← mvarId.assert boundName type (← mkFreshExprMVar type)
        mvarId := newGoal

    replaceMainGoal [mvarId]

--------------------------------------------------------------------------------
-- 3. The Unified Tactic
--------------------------------------------------------------------------------
macro "natify_uint8" : tactic => `(tactic|
  (
    inject_uint8_bounds
    try any_goals decide

    simp only [
      natify_uint8_eq_iff,
      UInt8.lt_iff_toNat_lt,
      UInt8.le_iff_toNat_le,
      UInt8.toNat_ofNat
    ] at *
  )
)
