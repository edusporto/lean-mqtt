import LeanMqtt

structure T (d : Nat) (p : d < 10)

def f (_t : T d p) := d

-- def x := f (T.mk : T 5 (by decide))

def main : IO Unit := do
  let stdin ← IO.getStdin

  let x ← stdin.getLine
  let x := match x.trim.toNat? with
  | none => panic! "not a number"
  | some n => n

  if h : x < 10 then
    let t : T x h := T.mk
    let n := @f _ _ t
    IO.println s!"Number: {n}"
  else
    IO.println s!"x over or equal 10"
