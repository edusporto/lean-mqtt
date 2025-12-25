import Batteries.Data.ByteArray

/--
  Available at
  [Batteries.Data.ByteArray](https://github.com/leanprover-community/batteries/blob/dff865b7ee7011518d59abfc101c368293173150/Batteries/Data/ByteArray.lean#L17).
-/
private theorem Helpers.getElem_eq_data_getElem (a : ByteArray) (h : i < a.size) :
    a[i] = a.data[i] := rfl

theorem Helpers.bytearray_tolist_eq_data_tolist (arr : ByteArray) :
    arr.toList = arr.data.toList := by
  let l := arr.data.toList

  have h_len : arr.size = l.length := by rfl

  -- Expose the `toList` loop (`toList.loop`)
  rw [ByteArray.toList]

  -- Prove the generalized specification of the loop
  -- Invariant: loop arr i r = r.reverse ++ l.drop i
  let rec loop_spec (i : Nat) (r : List UInt8) :
      ByteArray.toList.loop arr i r = r.reverse ++ l.drop i := by

    -- Unfold the loop step
    rw [ByteArray.toList.loop]

    -- Split execution based on the loop condition (i < arr.size)
    if h_lt : i < arr.size then
      -- CASE: The loop continues
      simp only [h_lt, ↓reduceIte]

      -- Apply inductive hypothesis to the next step
      rw [loop_spec (i + 1)]

      -- Simplify the list manipulation
      -- Goal: (arr.get! i :: r).reverse ++ l.drop (i + 1) = r.reverse ++ l.drop i
      simp only [List.reverse_cons, List.append_assoc]

      -- Now we need to prove: [arr.get! i] ++ l.drop (i + 1) = l.drop i
      -- This is conceptually: [l[i]] ++ l[i+1..] = l[i..]

      -- Convert ByteArray.get! to List.get
      -- Since i < arr.size, get! behaves exactly like get with a proof.z
      have h_idx_l : i < l.length := by rwa [←h_len]

      -- Note: ByteArray.get! checks bounds. Since h_lt holds, it returns the element.
      have h_val : arr.get! i = l.get ⟨i, h_idx_l⟩ := by
         -- This relates ByteArray.get! -> Array.get! -> Array.get -> List.get
        simp only [ByteArray.get!, ByteArray.size_data, h_lt, getElem!_pos, List.get_eq_getElem]
        apply Helpers.getElem_eq_data_getElem

      rw [h_val]

      -- Use the list property: l.drop i = l[i] :: l.drop (i+1)
      simp only [List.get_eq_getElem, List.cons_append, List.nil_append, List.getElem_cons_drop]

    else
      -- CASE: The loop terminates (i >= arr.size)
      simp only [h_lt, ↓reduceIte]

      -- Goal: r.reverse = r.reverse ++ l.drop i
      -- Since i >= length, drop i is empty
      have h_idx_ge : i ≥ l.length := by
        rw [←h_len]; exact Nat.le_of_not_lt h_lt

      rw [List.drop_eq_nil_of_le h_idx_ge]
      simp only [List.append_nil]

    termination_by arr.size - i

  -- Apply the spec to the initial call (i=0, r=[])
  have h_loop := loop_spec 0 []
  simp only [List.reverse_nil, List.nil_append, List.drop_zero] at h_loop
  exact h_loop

theorem Helpers.bytearray_list_roundtrip (arr : ByteArray) :
  arr.toList.toByteArray = arr := by
  -- Turn into easier goal `arr.data.toList.toByteArray = arr`
  rw [Helpers.bytearray_tolist_eq_data_tolist]

  -- Deconstruct
  cases arr with | mk data
  simp only

  let bs := data.toList

  -- Apply the lemma to the specific case
  apply ByteArray.ext
  simp only
  -- Goal: (data.toList.toByteArray).data = data

  -- Prove the property of the loop: it appends 'bs' to 'r'
  have loop_append (r : ByteArray) :
      (List.toByteArray.loop bs r).data.toList = r.data.toList ++ bs := by
    induction bs generalizing r with
    | nil =>
      simp only [List.toByteArray.loop, List.append_nil]
    | cons b tail ih =>
      simp only [List.toByteArray.loop]
      rw [ih (r.push b)]
      simp only [
        ByteArray.data_push, Array.toList_push,
        List.append_assoc, List.cons_append, List.nil_append
      ]

  -- Reduce Array equality to List equality
  have h_lists : data.toList.toByteArray.data.toList = data.toList := by
    rw [List.toByteArray]
    specialize loop_append ByteArray.empty
    simp at loop_append
    exact loop_append

  -- Conclude arrays are equal because their lists are equal
  apply Array.ext'
  exact h_lists
