import LeanMqtt.Core.Parser.Basic

theorem bytesParser_len (n : Nat) (l inp rest : List UInt8) :
  (bytesParser n).run inp = some (l, rest) → l.length = n := by
  simp [bytesParser]
  split
  · intro h_len
    contradiction
  · next h_len =>
    intro h
    simp at h
    have ⟨h_l, h_rest⟩ := h
    subst h_l
    simp [List.length_take]
    omega

theorem bytesParser_reconstruct (n : Nat) (input : List UInt8) (chunk rest : List UInt8) :
  (bytesParser n).run input = some (chunk, rest) → input = chunk ++ rest := by
  simp [bytesParser]
  split
  · intro; contradiction
  · next h_len =>
    simp
    intro h1 h2
    rw [←h1, ←h2]
    apply Eq.symm
    apply List.take_append_drop n input

theorem roundtrip_bytes (l : List UInt8) (rest : List UInt8) :
  (bytesParser l.length).run (l ++ rest) = some (l, rest) := by
  simp [bytesParser]
  split
  · omega
  · simp

theorem roundtrip_bytes_with_proof (l : List UInt8) (rest : List UInt8) :
  (bytesParserWithProof l.length).run (l ++ rest) = some (⟨l, rfl⟩, rest) := by
  simp [bytesParserWithProof]
  split
  · omega
  · simp

theorem bytesParserWithProof_eq_parser_success (n : Nat)
  (l : List UInt8) (inp rest : List UInt8) :
  (bytesParser n).run inp = some (l, rest) →
  ∃ h, (bytesParserWithProof n).run inp = some (⟨l, h⟩, rest) := by
  intro h_simple
  have h_len_parser := bytesParser_len _ _ _ _ h_simple
  simp only [bytesParser, bytesParserWithProof] at *
  simp only [bind_pure_comp, StateT.run_bind, StateT.run_get,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some
  ] at *
  split at h_simple
  · contradiction
  · next h_len =>
    simp only [StateT.run_map, StateT.run_set, Option.pure_def,
      Option.map_eq_map, Option.map_some, Option.some.injEq, Prod.mk.injEq
    ] at h_simple
    simp only [dif_neg h_len]
    simp only [StateT.run_map, StateT.run_set, Option.pure_def,
      Option.map_eq_map, Option.map_some, Option.some.injEq, Prod.mk.injEq,
      Subtype.mk.injEq, exists_and_left, exists_prop
    ]
    rcases h_simple with ⟨h_take, h_drop⟩
    exact ⟨h_take, h_len_parser, h_drop⟩
