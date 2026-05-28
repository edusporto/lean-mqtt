import LeanMqtt.Core.Parser.Proofs

/--
  `step_parser h → v state step_proof` is a tactic macro designed to unroll a single
  step of a `bind` operation in a parser reconstruction proof.

  It applies `Parser.bind_run_success` to crack the `bind` step `h`, extracting:
  - `v`: the parsed value from this step
  - `state`: the intermediate byte array state
  - `step_proof`: the proof that this specific step succeeded
  
  The original hypothesis `h` is then updated to represent the remainder of the parser
  execution.
-/
macro "step_parser" h:ident "→" v:ident state:ident step_proof:ident : tactic =>
  `(tactic| (
    replace $h := Parser.bind_run_success $h
    obtain ⟨$v:ident, $state:ident, $step_proof:ident, $h:ident⟩ := $h
  ))

/--
  `finish_parser h → eq_proof` is a tactic macro designed to unroll the final `pure`
  or `liftM` operation in a parser reconstruction proof.

  It attempts to apply either `Parser.pure_run_success` or `Parser.liftM_run_success`
  to the proof `h`, extracting:
  - `eq_proof`: the proof that the final parser result equals the expected value
  
  It then automatically substitutes the final state equivalence into the context,
  completing the unrolling process.
-/
macro "finish_parser" h:ident "→" eq_proof:ident : tactic =>
  `(tactic| (first 
    | replace $h := Parser.pure_run_success $h
      obtain ⟨$eq_proof:ident, $h:ident⟩ := $h
      subst $h
    | replace $h := Parser.liftM_run_success $h
      obtain ⟨$eq_proof:ident, $h:ident⟩ := $h
      subst $h
  ))
