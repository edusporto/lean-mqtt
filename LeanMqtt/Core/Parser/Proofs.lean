import LeanMqtt.Core.Parser.Basic

theorem Parser.bytes_len (n : Nat) (l inp rest : List UInt8) :
    (Parser.bytes n).run inp = some (l, rest) → l.length = n := by
  simp [Parser.bytes]
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

theorem Parser.bytes_reconstruct (n : Nat) (input chunk rest : List UInt8) :
    (Parser.bytes n).run input = some (chunk, rest) → input = chunk ++ rest := by
  simp [Parser.bytes]
  split
  · intro
    contradiction
  · next h_len =>
    simp
    intro h1 h2
    rw [← h1, ← h2]
    apply (List.take_append_drop n input).symm

theorem Parser.bytes_roundtrip (l rest : List UInt8) :
    (Parser.bytes l.length).run (l ++ rest) = some (l, rest) := by
  simp [Parser.bytes]
  split
  · omega
  · simp

theorem Parser.bytesWithProof_reconstruct (n : Nat) (input : List UInt8)
    (chunk : { l : List UInt8 // l.length = n }) (rest : List UInt8) :
    (Parser.bytesWithProof n).run input = some (chunk, rest) →
    input = chunk.val ++ rest := by
  simp [Parser.bytesWithProof]
  split
  · intro h
    contradiction
  · intro h
    simp at h
    obtain ⟨h_chunk, h_rest⟩ := h
    rw [←h_chunk, ←h_rest]
    exact (List.take_append_drop n input).symm

theorem Parser.bytesWithProof_roundtrip (l rest : List UInt8) :
    (Parser.bytesWithProof l.length).run (l ++ rest) = some (⟨l, rfl⟩, rest) := by
  simp [Parser.bytesWithProof]
  split
  · omega
  · simp

theorem Parser.bytes_imp_bytesWithProof (n : Nat) (l inp rest : List UInt8) :
    (Parser.bytes n).run inp = some (l, rest) →
    ∃ h, (Parser.bytesWithProof n).run inp = some (⟨l, h⟩, rest) := by
  intro h_simple
  have h_len_parser := Parser.bytes_len _ _ _ _ h_simple
  simp only [Parser.bytes, Parser.bytesWithProof] at *
  simp at *
  split at h_simple
  · contradiction
  · next h_len =>
    simp at h_simple
    simp [dif_neg h_len]
    rcases h_simple with ⟨h_take, h_drop⟩
    exact ⟨h_take, h_len_parser, h_drop⟩

theorem Parser.bind_run_success
    {α β : Type}
    (p1 : Parser α) (p2 : α → Parser β)
    (input rest : List UInt8) (res : β) :
    (p1 >>= p2).run input = some (res, rest) →
    ∃ a mid, p1.run input = some (a, mid) ∧ (p2 a).run mid = some (res, rest) := by
  simp [Option.bind]
  intro h
  split at h
  · contradiction
  · next pair h_p1 =>
    obtain ⟨a, mid⟩ := pair
    exact ⟨a, mid, h_p1, h⟩

theorem Parser.pure_run_success
    {α : Type}
    (a : α) (input rest : List UInt8) (res : α) :
    (pure a : Parser α).run input = some (res, rest) → res = a ∧ input = rest := by
  intro h
  simp [pure, StateT.run, StateT.pure] at h
  grind
