import Lean

open Lean Meta Elab Tactic

/-!
# Literal Crusher Tactic

This module provides the `crush_lits` tactic, which forces the Lean kernel to
evaluate and simplify closed `Nat` expressions (such as coerced literals or
arithmetic on constants) that standard `simp` often fails to reduce.

Specifically, we use this tactic to forcibly reduce coerced `VarInt`s into
`Nat`s, improving automation for proofs like `VarInt.parser_reconstruct`.
-/

/--
Traverses an expression and forces the reduction of closed `Nat` subexpressions.

It uses MetaM's `transform` to recursively inspect subexpressions. If it finds
a type-correct `Nat` expression that does not depend on free variables or metavariables,
it invokes `reduce` to compute its normal form. If that normal form is a raw numeric
literal, it swaps it into the expression.
-/
def cleanCastsAndLits (e : Expr) : MetaM Expr := do
  transform e (pre := fun sub => do
    -- Skip expressions that depend on local variables (like v') or metavariables.
    -- We only want to evaluate completely closed, concrete values.
    if sub.hasFVar || sub.hasExprMVar then
      return .continue

    -- Skip if it is already a clean, raw Nat literal (no work needed).
    if sub.rawNatLit?.isSome then
      return .continue

    try
      -- We only care about subexpressions that result in a Nat.
      let type ← inferType sub
      if type.isConstOf `Nat then
        -- Force the kernel to evaluate this closed expression.
        -- `reduce` performs full definitional reduction (similar to #eval/#reduce).
        let reduced ← reduce sub
        -- If it spits out a raw number, swap it in and stop recursing down this branch.
        if reduced.rawNatLit?.isSome then
          return .done reduced
    catch _ => pure ()

    return .continue
  )

/--
A tactic that forcibly reduces stubborn, coerced `Nat` literals in both the
local hypotheses and the target goal.

`crush_lits` is particularly useful when dealing with deeply nested type casts,
unfolded definitions, or arithmetic operations on constants that `simp` leaves
un-evaluated due to missing rewriting lemmas.

It is useful to run `simp at *` after this tactic for better cleanup.
-/
elab "crush_lits" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let mut newMvarId := mvarId

    -- Look through all hypotheses in the local context
    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let newType ← cleanCastsAndLits ldecl.type
      -- If any expressions inside the hypothesis were simplified, update the context
      if newType != ldecl.type then
        newMvarId ← newMvarId.changeLocalDecl ldecl.fvarId newType

    -- Clean up the target goal type
    let newGoalType ← cleanCastsAndLits (← newMvarId.getType)
    if newGoalType != (← newMvarId.getType) then
      newMvarId ← newMvarId.change newGoalType

    -- Replace the old goal with the newly cleaned goal
    replaceMainGoal [newMvarId]
