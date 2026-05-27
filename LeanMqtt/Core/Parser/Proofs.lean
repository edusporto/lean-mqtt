import LeanMqtt.Core.Parser.Basic

/-!
# Parser Proofs

This module contains fundamental theorems and lemmas for reasoning about
the `Parser` monad. It provides the essential building blocks for proving
roundtrip and reconstruction properties.
-/

/--
  Proves that if `Parser.bytes n` succeeds and returns a list `l`,
  the length of `l` is exactly `n`.

  This theorem establishes the fundamental correctness of the `bytes`
  parser with respect to the requested length.
-/
theorem Parser.bytes_len {n : Nat} {input l rest : List UInt8} :
    (Parser.bytes n).run input = some (l, rest) → l.length = n := by
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

/--
  Proves the roundtrip property for `Parser.bytes`.

  If we serialize a list `l` and append `rest` to it, parsing exactly
  `l.length` bytes will successfully recover the original list `l`
  and leave `rest` unconsumed.
-/
theorem Parser.bytes_roundtrip (l rest : List UInt8):
    (Parser.bytes l.length).run (l ++ rest) = some (l, rest) := by
  simp [Parser.bytes]
  split
  · omega
  · simp

/--
  Proves the reconstruction property for `Parser.bytes`.

  If `Parser.bytes n` successfully parses a `chunk` and leaves `rest`,
  then the original `input` must be exactly the concatenation of
  `chunk` and `rest` (`chunk ++ rest`). This guarantees that `bytes`
  doesn't skip or alter any bytes from the input stream.
-/
theorem Parser.bytes_reconstruct {n : Nat} {input chunk rest : List UInt8} :
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

/--
  Proves the roundtrip property for `Parser.bytesWithProof`.

  If we serialize a list `l` and append `rest` to it, parsing exactly
  `l.length` bytes using `bytesWithProof` will successfully recover `l`
  (along with the trivial proof `rfl` that its length is `l.length`)
  and leave `rest` unconsumed.
-/
theorem Parser.bytesWithProof_roundtrip (l rest : List UInt8) :
    (Parser.bytesWithProof l.length).run (l ++ rest) = some (⟨l, rfl⟩, rest) := by
  simp [Parser.bytesWithProof]
  split
  · omega
  · simp

/--
  Proves the reconstruction property for `Parser.bytesWithProof`.

  Similar to `Parser.bytes_reconstruct`, this guarantees that if we parse
  `n` bytes and get a `chunk` (which is a dependent pair of a list and a
  proof of its length), the original `input` is the concatenation of the
  parsed `chunk.val` and the `rest`.
-/
theorem Parser.bytesWithProof_reconstruct {n : Nat} {input : List UInt8}
    {chunk : { l : List UInt8 // l.length = n }} {rest : List UInt8} :
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

/--
  Proves that the success of `Parser.bytes` implies the success of
  `Parser.bytesWithProof` on the same input.

  Since `bytesWithProof` is simply `bytes` combined with a length check
  that is guaranteed to succeed if `bytes` succeeds, we can always
  upgrade a successful `bytes` parse into a `bytesWithProof` parse.
-/
theorem Parser.bytes_imp_bytesWithProof {n : Nat} {l inp rest : List UInt8} :
    (Parser.bytes n).run inp = some (l, rest) →
    ∃ h, (Parser.bytesWithProof n).run inp = some (⟨l, h⟩, rest) := by
  intro h_simple
  have h_len_parser := Parser.bytes_len h_simple
  simp only [Parser.bytes, Parser.bytesWithProof] at *
  simp at *
  split at h_simple
  · contradiction
  · next h_len =>
    simp at h_simple
    simp [dif_neg h_len]
    rcases h_simple with ⟨h_take, h_drop⟩
    exact ⟨h_take, h_len_parser, h_drop⟩

/--
  Deconstructs a successful run of a monadic bind (`p1 >>= p2`) into its
  constituent parts.

  If parsing `p1 >>= p2` succeeds and returns `result` along with `rest`,
  then there must exist some intermediate parsed value (`midVal`) and an
  intermediate byte state (`midBytes`) such that `p1` succeeds,
  and `p2` succeeds on the rest.

  In other words, we deconstruct a step in do-notation into an intermediate
  parsed value and an intermediate input rest. This is because the following:
  ```
  (p1 >>= p2).run input
  ```
  is the same as:
  ```
  (do let midVal ← p1
      p2 midVal).run input
  ```
-/
theorem Parser.bind_run_success
    {α β : Type}
    {p1 : Parser α} {p2 : α → Parser β}
    {input rest : List UInt8} {result : β} :
    (p1 >>= p2).run input = some (result, rest) →
    ∃ midVal midBytes,
      p1.run input = some (midVal, midBytes) ∧
      (p2 midVal).run midBytes = some (result, rest) := by
  simp [Option.bind]
  intro h
  split at h
  · contradiction
  · next pair h_p1 =>
    obtain ⟨a, mid⟩ := pair
    exact ⟨a, mid, h_p1, h⟩

/--
  Deconstructs a successful run of `pure val` into its constituent parts.

  If parsing `pure val` succeeds and returns `result` along with `rest`,
  then `result` must be exactly `val`, and the input must not have been
  consumed, meaning `input` is equal to `rest`.`.
-/
theorem Parser.pure_run_success
    {α : Type}
    {val : α} {input rest : List UInt8} {result : α} :
    (pure val : Parser α).run input = some (result, rest) →
    result = val ∧ input = rest := by
  intro h
  simp [pure, StateT.run, StateT.pure] at h
  grind

/--
  Deconstructs a successful run of `liftM opt` into its constituent parts.

  If parsing `liftM opt` succeeds and returns `result` along with `rest`,
  then the underlying `Option` must have been `some result`, and the input
  must not have been consumed, meaning `input` is equal to `rest`.

  In other words, we deconstruct an option unwrapping step in do-notation.
  This is because the following:
  ```
  (liftM opt).run input
  ```
  is the same as:
  ```
  (do let result ← opt
      pure result).run input
  ```
-/
theorem Parser.liftM_run_success
    {α : Type}
    {opt : Option α} {input rest : List UInt8} {result : α} :
    (liftM opt : Parser α).run input = some (result, rest) →
    opt = some result ∧ input = rest := by
  intro h
  simp [Option.bind] at h
  split at h
  · contradiction
  · next =>
    injection h with h_eq
    injection h_eq with h_res h_rest
    subst h_res h_rest
    exact ⟨rfl, rfl⟩
