import SuperpermutationUpperBound.Transport.Local

/-! Literal endpoint identities for the full/deficit-two local transport.
All statements retain actual ordered tuples, without identifying endpoints.
-/
namespace SuperpermutationUpperBound.Transport

variable {α : Type}

@[simp] theorem insertLetter_cons_succ (a : α) (x : List α) (z : α) (j : Nat) :
    insertLetter (a :: x) z (j + 1) = a :: insertLetter x z j := by
  simp [insertLetter, List.take_succ_cons]

theorem take_insertLetter (x : List α) (z : α) (j k : Nat)
    (hj : j ≤ k) (hk : k ≤ x.length) :
    (insertLetter x z j).take (k + 1) = insertLetter (x.take k) z j := by
  induction x generalizing j k with
  | nil =>
    have hk0 : k = 0 := by simp only [List.length_nil] at hk; omega
    have hj0 : j = 0 := by omega
    subst k; subst j
    simp [insertLetter]
  | cons a x ih =>
    cases j with
    | zero => simp [insertLetter, List.take_succ_cons]
    | succ j =>
      cases k with
      | zero => exfalso; omega
      | succ k =>
        simpa only [insertLetter_cons_succ, List.take_succ_cons] using
          congrArg (List.cons a) (ih j k (by omega) (by simp only [List.length_cons] at hk; omega))

theorem drop_one_insertLetter (x : List α) (z : α) (j : Nat)
    (hj : 1 ≤ j) (hx : 1 ≤ x.length) :
    (insertLetter x z j).drop 1 = insertLetter (x.drop 1) z (j - 1) := by
  cases x with
  | nil => simp at hx
  | cons a x =>
    have hj' : j = (j - 1) + 1 := by omega
    conv => lhs; arg 2; rw [hj']
    simp only [insertLetter_cons_succ, List.drop_succ_cons, List.drop_zero]

theorem row_full_tail (x : List α) (s : α) (hx : 2 ≤ x.length) :
    (Row.mk x s x.length).tail = (x.drop 1).take (x.length - 2) := by
  change (rot x (x.length + 1)).take (x.length - 2) = _
  rw [Nat.add_comm x.length 1, rot_add_length,
    rot_eq_drop_append_take_of_le x 1 (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem full_insert_head (x : List α) (z s : α) (j : Nat)
    (hx : 2 ≤ x.length) (hj : j ≤ x.length - 2) :
    (Row.mk (insertLetter x z j) s (x.length + 1)).head =
      insertLetter (Row.mk x s x.length).head z j := by
  unfold Row.head
  rw [insertLetter_length]
  have hlen : x.length + 1 - 2 = (x.length - 2) + 1 := by omega
  rw [hlen, take_insertLetter x z j (x.length - 2) hj (by omega)]

/-- Every nonexceptional full row translates its insertion port one step left. -/
theorem full_singleton_tail (x : List α) (z s : α) (j : Nat)
    (hx : 2 ≤ x.length) (hjlo : 1 ≤ j) (hjhi : j ≤ x.length - 2) :
    (Row.mk (insertLetter x z j) s (x.length + 1)).tail =
      insertLetter (Row.mk x s x.length).tail z (j - 1) := by
  have hnew : (Row.mk (insertLetter x z j) s (x.length + 1)).tail =
      ((insertLetter x z j).drop 1).take (x.length + 1 - 2) := by
    simpa only [insertLetter_length] using
      row_full_tail (insertLetter x z j) s (by simp; omega)
  rw [hnew, drop_one_insertLetter x z j hjlo (by omega), row_full_tail x s hx]
  have hlen : x.length + 1 - 2 = (x.length - 2) + 1 := by omega
  rw [hlen, take_insertLetter (x.drop 1) z (j - 1) (x.length - 2)
    (by omega) (by simp only [List.length_drop]; omega)]

theorem row_head_append_two (u : List α) (p b s : α) (L : Nat) :
    (Row.mk (u ++ [p, b]) s L).head = u := by
  simp only [Row.head, List.length_append, List.length_cons, List.length_nil]
  have hn : u.length + (0 + 1 + 1) - 2 = u.length := by omega
  rw [hn, List.take_append_length]

theorem rot_last_append (u : List α) (b : α) :
    rot (u ++ [b]) u.length = b :: u := by
  rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
  simp only [List.drop_append_length, List.take_append_length, List.singleton_append]

theorem row_short_tail_append_two (u : List α) (p b s : α) (hu : 1 ≤ u.length) :
    (Row.mk (u ++ [p, b]) s u.length).tail = b :: u.take (u.length - 1) := by
  unfold Row.tail
  change (rot (u ++ [p, b]) (u.length + 1)).take
    ((u ++ [p, b]).length - 2) = _
  have hbase : u ++ [p, b] = (u ++ [p]) ++ [b] := by simp
  have hrot : rot (u ++ [p, b]) (u.length + 1) = b :: (u ++ [p]) := by
    rw [hbase]
    simpa using rot_last_append (u ++ [p]) b
  rw [hrot]
  have hlen : (u ++ [p, b]).length - 2 = (u.length - 1) + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [hlen, List.take_succ_cons, List.take_append_of_le_length (by omega)]

theorem short_exceptional_first_head (u : List α) (z p b s : α) :
    (Row.mk (u ++ [z, p, b]) s (u.length + 1)).head = u ++ [z] := by
  simpa only [List.append_assoc, List.singleton_append] using
    row_head_append_two (u ++ [z]) p b s (u.length + 1)

theorem short_exceptional_first_tail (u : List α) (z p b s : α) :
    (Row.mk (u ++ [z, p, b]) s (u.length + 1)).tail = b :: u := by
  have h := row_short_tail_append_two (u ++ [z]) p b s (by simp)
  simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.take_append_length, List.append_assoc, List.singleton_append] using h

theorem short_exceptional_second_head (u : List α) (z p b s : α) :
    (Row.mk (b :: (u ++ [p, z])) s (u.length + 1)).head = b :: u := by
  simpa only [List.cons_append] using
    row_head_append_two (b :: u) p z s (u.length + 1)

theorem short_exceptional_second_tail (u : List α) (z p b s : α) (hu : 1 ≤ u.length) :
    (Row.mk (b :: (u ++ [p, z])) s (u.length + 1)).tail =
      z :: b :: u.take (u.length - 1) := by
  have h := row_short_tail_append_two (b :: u) p z s (by simp)
  have hlen : u.length = (u.length - 1) + 1 := by omega
  have ht : (b :: u).take u.length = b :: u.take (u.length - 1) := by
    calc
      (b :: u).take u.length = (b :: u).take ((u.length - 1) + 1) :=
        congrArg (fun j => (b :: u).take j) hlen
      _ = _ := List.take_succ_cons
  simpa only [List.length_cons, Nat.add_sub_cancel, List.cons_append,
    ht] using h

theorem short_exceptional_compatible (u : List α) (z p b s : α) :
    Row.Compatible (Row.mk (u ++ [z, p, b]) s (u.length + 1))
      (Row.mk (b :: (u ++ [p, z])) s (u.length + 1)) := by
  unfold Row.Compatible
  rw [short_exceptional_first_tail, short_exceptional_second_head]

theorem insertLetter_append_of_le (u v : List α) (z : α) (j : Nat) (hj : j ≤ u.length) :
    insertLetter (u ++ v) z j = insertLetter u z j ++ v := by
  simp only [insertLetter, List.take_append_of_le_length hj,
    List.drop_append_of_le_length hj, List.append_assoc]

theorem short_singleton_head (u : List α) (z p b s : α) (j : Nat) (hj : j < u.length) :
    (Row.mk (insertLetter (u ++ [p, b]) z j) s (u.length + 1)).head =
      insertLetter (Row.mk (u ++ [p, b]) s u.length).head z j := by
  rw [insertLetter_append_of_le u [p, b] z j (by omega),
    row_head_append_two, row_head_append_two]

/-- Every nonexceptional short row translates its insertion port one step right. -/
theorem short_singleton_tail (u : List α) (z p b s : α) (j : Nat) (hj : j < u.length) :
    (Row.mk (insertLetter (u ++ [p, b]) z j) s (u.length + 1)).tail =
      insertLetter (Row.mk (u ++ [p, b]) s u.length).tail z (j + 1) := by
  rw [insertLetter_append_of_le u [p, b] z j (by omega)]
  have hnew := row_short_tail_append_two (insertLetter u z j) p b s (by simp)
  simp only [insertLetter_length, Nat.add_sub_cancel] at hnew
  rw [hnew, row_short_tail_append_two u p b s (by omega), insertLetter_cons_succ]
  have hlen : u.length = (u.length - 1) + 1 := by omega
  have ht : (insertLetter u z j).take u.length = insertLetter (u.take (u.length - 1)) z j := by
    calc
      (insertLetter u z j).take u.length =
          (insertLetter u z j).take ((u.length - 1) + 1) :=
        congrArg (fun k => (insertLetter u z j).take k) hlen
      _ = _ := take_insertLetter u z j (u.length - 1) (by omega) (by omega)
  rw [ht]

theorem full_exceptional_first_head (a : α) (u : List α) (z b s : α) :
    (Row.mk (z :: a :: (u ++ [b])) s (u.length + 3)).head =
      z :: (a :: u).take u.length := by
  unfold Row.head
  have hlen : (z :: a :: (u ++ [b])).length - 2 = u.length + 1 := by simp
  rw [hlen, List.take_succ_cons]
  change z :: ((a :: u) ++ [b]).take u.length = _
  rw [List.take_append_of_le_length (by simp)]

theorem full_exceptional_first_tail (a : α) (u : List α) (z b s : α) :
    (Row.mk (z :: a :: (u ++ [b])) s (u.length + 3)).tail = a :: u := by
  have h := row_full_tail (z :: a :: (u ++ [b])) s (by simp)
  have hlen : (z :: a :: (u ++ [b])).length = u.length + 3 := by simp
  rw [hlen] at h
  rw [h]
  simp only [List.drop_succ_cons, List.drop_zero]
  have hn : u.length + 3 - 2 = u.length + 1 := by omega
  rw [hn, List.take_succ_cons, List.take_append_length]

theorem full_exceptional_second_head (a : α) (u : List α) (z b s : α) :
    (Row.mk (a :: (u ++ [z, b])) s (u.length + 3)).head = a :: u := by
  simpa only [List.cons_append] using row_head_append_two (a :: u) z b s (u.length + 3)

theorem full_exceptional_second_tail (a : α) (u : List α) (z b s : α) :
    (Row.mk (a :: (u ++ [z, b])) s (u.length + 3)).tail = u ++ [z] := by
  have h := row_full_tail (a :: (u ++ [z, b])) s (by simp)
  have hlen : (a :: (u ++ [z, b])).length = u.length + 3 := by simp
  rw [hlen] at h
  rw [h]
  simp only [List.drop_succ_cons, List.drop_zero]
  have hn : u.length + 3 - 2 = (u ++ [z]).length := by simp
  rw [hn]
  have hb : u ++ [z, b] = (u ++ [z]) ++ [b] := by simp
  rw [hb, List.take_append_length]

theorem full_exceptional_compatible (a : α) (u : List α) (z b s : α) :
    Row.Compatible (Row.mk (z :: a :: (u ++ [b])) s (u.length + 3))
      (Row.mk (a :: (u ++ [z, b])) s (u.length + 3)) := by
  unfold Row.Compatible
  rw [full_exceptional_first_tail, full_exceptional_second_head]

theorem insertLetter_at_length (x : List α) (z : α) :
    insertLetter x z x.length = x ++ [z] := by simp [insertLetter]

theorem full_final_base (a : α) (u : List α) (z b : α) :
    insertLetter (a :: (u ++ [b])) z (u.length + 1) = a :: (u ++ [z, b]) := by
  rw [insertLetter_cons_succ, insertLetter_append_of_le u [b] z u.length (by omega),
    insertLetter_at_length]
  simp only [List.append_assoc, List.singleton_append]

theorem short_exceptional_first_base (u : List α) (z p b : α) :
    insertLetter (u ++ [p, b]) z u.length = u ++ [z, p, b] := by
  rw [insertLetter_append_of_le u [p, b] z u.length (by omega), insertLetter_at_length]
  simp only [List.append_assoc, List.singleton_append]

theorem short_exceptional_second_base (u : List α) (z p b : α) :
    rot (u ++ [p, b]) (u.length + 1) ++ [z] = b :: (u ++ [p, z]) := by
  have hx : u ++ [p, b] = (u ++ [p]) ++ [b] := by simp
  have hrot : rot (u ++ [p, b]) (u.length + 1) = b :: (u ++ [p]) := by
    rw [hx]
    simpa only [List.length_append, List.length_singleton] using rot_last_append (u ++ [p]) b
  rw [hrot]
  simp only [List.cons_append, List.append_assoc, List.nil_append]

/-- The exceptional short path goes from the final old port to port zero. -/
theorem short_exceptional_path (u : List α) (z p b s : α) (hu : 1 ≤ u.length) :
    let old := Row.mk (u ++ [p, b]) s u.length
    let first := Row.mk (u ++ [z, p, b]) s (u.length + 1)
    let last := Row.mk (b :: (u ++ [p, z])) s (u.length + 1)
    first.head = insertLetter old.head z u.length ∧
      Row.Compatible first last ∧ last.tail = insertLetter old.tail z 0 := by
  dsimp only
  refine ⟨?_, short_exceptional_compatible u z p b s, ?_⟩
  · rw [short_exceptional_first_head, row_head_append_two, insertLetter_at_length]
  · rw [short_exceptional_second_tail u z p b s hu,
      row_short_tail_append_two u p b s hu]
    simp only [insertLetter, List.take_zero, List.nil_append, List.drop_zero,
      List.singleton_append]

/-- The exceptional full path goes from old port zero to the final port. -/
theorem full_exceptional_path (a : α) (u : List α) (z b s : α) :
    let old := Row.mk (a :: (u ++ [b])) s (u.length + 2)
    let first := Row.mk (z :: a :: (u ++ [b])) s (u.length + 3)
    let last := Row.mk (a :: (u ++ [z, b])) s (u.length + 3)
    first.head = insertLetter old.head z 0 ∧
      Row.Compatible first last ∧ last.tail = insertLetter old.tail z u.length := by
  dsimp only
  refine ⟨?_, full_exceptional_compatible a u z b s, ?_⟩
  · rw [full_exceptional_first_head]
    simp only [Row.head, List.length_cons, List.length_append,
      insertLetter, List.take_zero, List.nil_append,
      List.drop_zero, List.singleton_append]
    change z :: (a :: u).take u.length = z :: ((a :: u) ++ [b]).take u.length
    rw [List.take_append_of_le_length (by simp)]
  · have ht : (Row.mk (a :: (u ++ [b])) s (u.length + 2)).tail = u := by
      have h := row_full_tail (a :: (u ++ [b])) s (by simp)
      simpa using h
    rw [full_exceptional_second_tail, ht, insertLetter_at_length]

end SuperpermutationUpperBound.Transport
