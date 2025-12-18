theorem drop_eq_get_cons : ∀ {n} {l : List α} (h), l.drop n = l.get ⟨n, h⟩ :: l.drop (n + 1)
  | 0, _ :: _, _ => rfl
  | n + 1, _ :: _, _ => @drop_eq_get_cons α n _ _

-- We use `arr.data.toList` instead of `arr.toList` to leverage `Array` theorems
theorem bytearray_list_roundtrip (arr : ByteArray) :
  arr.data.toList.toByteArray = arr := by
  sorry
  -- -- 1. Characterize List.toByteArray
  -- -- Prove that the loop essentially appends the list 'bs' to the array 'r'
  -- have loop_push (bs : List UInt8) (r : ByteArray) :
  --   (List.toByteArray.loop bs r).data = r.data ++ bs := by
  --   induction bs generalizing r with
  --   | nil =>
  --     simp [List.toByteArray.loop]
  --   | cons b bs ih =>
  --     simp [List.toByteArray.loop]
  --     rw [ih (r.push b)]
  --     -- ByteArray.push wraps Array.push, which appends to the underlying list
  --     simp [ByteArray.push, Array.push]

  -- -- 2. Characterize toList
  -- -- Prove that the loop builds the list from index 'i' onwards
  -- let rec loop_get (i : Nat) (r : List UInt8) (hi : i ≤ arr.size) :
  --   ByteArray.toList.loop arr i r = r.reverse ++ (arr.data.toList.drop i) := by
  --   unfold ByteArray.toList.loop
  --   split
  --   next h_lt =>
  --     -- Recursive step
  --     rw [loop_get (i+1) (arr.get! i :: r) h_lt]
  --     -- Simplify list arithmetic: r.reverse ++ [arr[i]] ++ drop (i+1)
  --     -- Using property: drop i L = L[i] :: drop (i+1) L
  --     simp
  --     have : arr.data.toList.drop i = arr.get! i :: arr.data.toList.drop (i + 1) := by
  --       apply List.drop_eq_get_cons
  --       rw [Array.size, ← List.length_toArray] at h_lt
  --       exact h_lt
  --     rw [this, List.append_assoc, List.reverse_cons, List.singleton_append]
  --     rfl
  --   next h_nlt =>
  --     -- Base case: i >= arr.size
  --     have : i = arr.size := Nat.le_antisymm hi (Nat.ge_of_not_lt h_nlt)
  --     subst this
  --     simp [List.drop_length_le (Nat.le_refl _)]
  --   termination_by arr.size - i
  --   decreasing_by decreasing_trivial_pre_omega

  -- -- 3. Combine to prove the roundtrip
  -- apply ByteArray.ext
  -- simp [ByteArray.toList, List.toByteArray]
  -- rw [loop_get 0 [] (Nat.zero_le _)]
  -- rw [loop_push]
  -- simp
