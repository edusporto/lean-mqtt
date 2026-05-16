import Lean

open Lean Meta Elab Tactic

--------------------------------------------------------------------------------
-- Literal Crusher
--------------------------------------------------------------------------------

def cleanCastsAndLits (e : Expr) : MetaM Expr := do
  transform e (pre := fun sub => do
    -- 1. Skip expressions that depend on local variables (like v')
    if sub.hasFVar || sub.hasExprMVar then
      return .continue

    -- 2. Skip if it is already a clean, raw Nat literal
    if sub.rawNatLit?.isSome then
      return .continue

    try
      -- 3. We only care about subexpressions that result in a Nat
      let type ← inferType sub
      if type.isConstOf `Nat then
        -- 4. Force the kernel to evaluate this closed expression
        let reduced ← reduce sub
        -- 5. If it spits out a raw number, swap it in and stop recursing here!
        if reduced.rawNatLit?.isSome then
          return .done reduced
    catch _ => pure ()

    return .continue
  )

elab "crush_lits" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let mut newMvarId := mvarId

    for ldecl in (← getLCtx) do
      if ldecl.isImplementationDetail then continue
      let newType ← cleanCastsAndLits ldecl.type
      if newType != ldecl.type then
        newMvarId ← newMvarId.changeLocalDecl ldecl.fvarId newType

    let newGoalType ← cleanCastsAndLits (← newMvarId.getType)
    if newGoalType != (← newMvarId.getType) then
      newMvarId ← newMvarId.change newGoalType

    replaceMainGoal [newMvarId]
