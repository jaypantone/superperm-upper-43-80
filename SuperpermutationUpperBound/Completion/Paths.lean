import SuperpermutationUpperBound.Completion.Local
import SuperpermutationUpperBound.Transport.IndexedPaths

/-! Completion paths indexed by the same literal insertion ports as transport.
The exceptional short path includes both repair rows and both deficit-three lifts. -/
namespace SuperpermutationUpperBound.Completion

variable {α : Type}
open Transport

def shortPathAt (r : Row α) (z : α) (j : Nat) : List (Row α) :=
  if j < r.base.length - 2 then [liftRow r z j]
  else [liftRow r z (r.base.length - 2), repairRow r z (r.base.length - 2),
    repairRow r z (r.base.length - 1), liftRow r z (r.base.length - 1)]

def portPath (r : Row α) (z : α) (j : Nat) : List (Row α) :=
  if r.visible = r.base.length then Transport.fullPathAt r z j else shortPathAt r z j

theorem liftRow_eq_fullAt {r : Row α} (z : α) {j : Nat}
    (hf : r.visible = r.base.length) (hj : j < r.base.length) :
    liftRow r z j = fullAt r z j := by
  simp [liftRow, fullAt, hf, hj]

theorem liftRow_eq_shortAt {r : Row α} (z : α) {j : Nat}
    (hs : r.visible = r.base.length - 2) (hj : j < r.base.length - 2) :
    liftRow r z j = shortAt r z j := by
  have he : r.base.length - 2 + 1 = r.base.length - 1 := by omega
  simp [liftRow, shortAt, hs, hj, he]

private theorem insert_before_last (u : List α) (p z b : α) :
    insertLetter (u ++ [p,b]) z (u.length + 1) = u ++ [p,z,b] := by
  have he : u ++ [p,b] = (u ++ [p]) ++ [b] := by simp
  rw [he, show u.length + 1 = (u ++ [p]).length by simp,
    insertLetter_append_of_le _ _ _ _ (by omega), insertLetter_at_length]
  simp

private theorem rot_append_cut (u v : List α) : rot (u ++ v) u.length = v ++ u := by
  rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
  simp

private theorem short_exceptional_shapes {r : Row α} (z : α)
    (hs : r.visible = r.base.length - 2) {u : List α} {p b : α}
    (hx : r.base = u ++ [p,b]) :
    liftRow r z (r.base.length - 2) = ⟨u ++ [z,p,b], r.satellite, u.length⟩ ∧
    liftRow r z (r.base.length - 1) = ⟨u ++ [p,z,b], r.satellite, u.length⟩ := by
  constructor
  · simp [liftRow, hs, hx, short_exceptional_first_base]
  · simp [liftRow, hs, hx, insert_before_last]

private theorem deficit_three_head (u : List α) (a b c s : α) :
    (Row.mk (u ++ [a,b,c]) s u.length).head = u ++ [a] := by
  change (u ++ [a,b,c]).take ((u ++ [a,b,c]).length - 2) = _
  have he : u ++ [a,b,c] = (u ++ [a]) ++ [b,c] := by simp
  rw [he]
  simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel] using
    (@List.take_append_length α (u ++ [a]) [b,c])

private theorem deficit_three_tail (u : List α) (a b c s : α) (hu : 1 ≤ u.length) :
    (Row.mk (u ++ [a,b,c]) s u.length).tail = b :: c :: u.take (u.length - 1) := by
  change (rot (u ++ [a,b,c]) (u.length + 1)).take
    ((u ++ [a,b,c]).length - 2) = _
  have he : u ++ [a,b,c] = (u ++ [a]) ++ [b,c] := by simp
  have hl : (u ++ [a,b,c]).length - 2 = (u.length - 1) + 2 := by simp; omega
  rw [hl, he, show u.length + 1 = (u ++ [a]).length by simp, rot_append_cut]
  simp only [List.cons_append, List.nil_append, List.take_succ_cons]
  rw [List.take_append_of_le_length (by omega)]

/-- The four completion rows meet on literal tuples, including both repair interfaces. -/
theorem short_exceptional_endpoints {r : Row α} (z : α)
    (hn : 3 ≤ r.base.length) (hs : r.visible = r.base.length - 2) :
    (liftRow r z (r.base.length - 2)).head = insertLetter r.head z (r.base.length - 2) ∧
    (liftRow r z (r.base.length - 2)).Compatible (repairRow r z (r.base.length - 2)) ∧
    (repairRow r z (r.base.length - 2)).Compatible (repairRow r z (r.base.length - 1)) ∧
    (repairRow r z (r.base.length - 1)).Compatible (liftRow r z (r.base.length - 1)) ∧
    (liftRow r z (r.base.length - 1)).tail = insertLetter r.tail z 0 := by
  obtain ⟨u,p,b,hx⟩ := exists_append_two r.base (by omega)
  have hlen : r.base.length = u.length + 2 := by simp [hx]
  have hu : 1 ≤ u.length := by omega
  have hshape := short_exceptional_shapes z hs hx
  have hh : r.head = u := by simp [Row.head, hx]
  have ht : r.tail = b :: u.take (u.length - 1) := by
    have hr : Row.mk (u ++ [p,b]) r.satellite u.length = r := by cases r; simp_all
    rw [← hr]
    exact row_short_tail_append_two u p b r.satellite hu
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hshape.1, deficit_three_head, hh, hlen]
    simp [insertLetter_at_length]
  · change (liftRow r z (r.base.length - 2)).tail = _
    rw [hshape.1, deficit_three_tail _ _ _ _ _ hu, repairRow_head, hx]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.add_sub_cancel]
    rw [rot_append_cut]
    have he : u.length + 2 - 1 = (u.length - 1) + 2 := by omega
    rw [he]
    simp
  · have h := repairRow_compatible_next r z (r.base.length - 2) (by omega)
    simpa only [show r.base.length - 2 + 1 = r.base.length - 1 by omega] using h
  · change (repairRow r z (r.base.length - 1)).tail = _
    rw [repairRow_final_tail r z (by omega), hshape.2, deficit_three_head, hx]
    have he : u ++ [p,b] = (u ++ [p]) ++ [b] := by simp
    rw [he]
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel] using
      (@List.take_append_length α (u ++ [p]) [b])
  · rw [hshape.2, deficit_three_tail _ _ _ _ _ hu, ht]
    simp [insertLetter]

theorem shortPathAt_nonempty (r : Row α) (z : α) (j : Nat) : shortPathAt r z j ≠ [] := by
  unfold shortPathAt
  split <;> simp

theorem portPath_nonempty (r : Row α) (z : α) (j : Nat) : portPath r z j ≠ [] := by
  unfold portPath
  split
  · exact Transport.fullPathAt_nonempty r z j
  · exact shortPathAt_nonempty r z j

theorem shortPathAt_internal {r : Row α} (z : α) (j : Nat)
    (hn : 3 ≤ r.base.length) (hs : r.visible = r.base.length - 2) :
    RowTrailCompatible ((shortPathAt r z j).head (shortPathAt_nonempty r z j))
      (shortPathAt r z j).tail := by
  by_cases hj : j < r.base.length - 2
  · simp only [shortPathAt, if_pos hj, List.head_cons, List.tail_cons, RowTrailCompatible]
  · simp only [shortPathAt, if_neg hj, List.head_cons, List.tail_cons, RowTrailCompatible]
    have he := short_exceptional_endpoints z hn hs
    exact ⟨he.2.1, he.2.2.1, he.2.2.2.1, True.intro⟩

theorem portPath_internal {r : Row α} (z : α) (j : Nat)
    (hn : 3 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    RowTrailCompatible ((portPath r z j).head (portPath_nonempty r z j))
      (portPath r z j).tail := by
  by_cases hf : r.visible = r.base.length
  · simpa only [portPath, if_pos hf] using Transport.fullPathAt_internal r z j (by omega)
  · simpa only [portPath, if_neg hf] using shortPathAt_internal z j hn (hkind.resolve_left hf)

theorem shortPathAt_endpoints {r : Row α} (z : α) {j : Nat} (hn : 3 ≤ r.base.length)
    (hs : r.visible = r.base.length - 2) (hj : j < r.base.length - 1) :
    ((shortPathAt r z j).head?).map Row.head = some (insertLetter r.head z j) ∧
      ((shortPathAt r z j).getLast?).map Row.tail = some (insertLetter r.tail z (portTarget r j)) := by
  have hf : r.visible ≠ r.base.length := by omega
  by_cases hjshort : j < r.base.length - 2
  · have he := shortAt_singleton_endpoints r z j hn hs hjshort
    constructor
    · simpa [shortPathAt, hjshort, liftRow_eq_shortAt z hs hjshort] using congrArg some he.1
    · simpa [shortPathAt, hjshort, liftRow_eq_shortAt z hs hjshort,
        portTarget_short_singleton hf hjshort] using congrArg some he.2
  · have hjlast : j = r.base.length - 2 := by omega
    subst j
    have he := short_exceptional_endpoints z hn hs
    constructor
    · simpa [shortPathAt] using congrArg some he.1
    · simpa [shortPathAt, portTarget_short_final hn hf] using congrArg some he.2.2.2.2

theorem portPath_endpoints {r : Row α} (z : α) {j : Nat} (hn : 3 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hj : j < r.base.length - 1) :
    ((portPath r z j).head?).map Row.head = some (insertLetter r.head z j) ∧
      ((portPath r z j).getLast?).map Row.tail = some (insertLetter r.tail z (portTarget r j)) := by
  by_cases hf : r.visible = r.base.length
  · simpa only [portPath, if_pos hf] using Transport.fullPathAt_endpoints z hn hf hj
  · simpa only [portPath, if_neg hf] using shortPathAt_endpoints z hn (hkind.resolve_left hf) hj

theorem portPath_head {r : Row α} (z : α) {j : Nat} (hn : 3 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hj : j < r.base.length - 1) :
    ((portPath r z j).head (portPath_nonempty r z j)).head = insertLetter r.head z j := by
  have h := (portPath_endpoints z hn hkind hj).1
  have hopt : (portPath r z j).head? = some ((portPath r z j).head (portPath_nonempty r z j)) :=
    List.head?_eq_some_head _
  rw [hopt, Option.map_some, Option.some.injEq] at h
  exact h

theorem portPath_last_tail {r : Row α} (z : α) {j : Nat} (hn : 3 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hj : j < r.base.length - 1) :
    ((portPath r z j).getLast (portPath_nonempty r z j)).tail =
      insertLetter r.tail z (portTarget r j) := by
  have h := (portPath_endpoints z hn hkind hj).2
  have hopt : (portPath r z j).getLast? = some ((portPath r z j).getLast (portPath_nonempty r z j)) :=
    List.getLast?_eq_some_getLast _
  rw [hopt, Option.map_some, Option.some.injEq] at h
  exact h

theorem completeRows_eq_fullRows {r : Row α} (z : α)
    (hf : r.visible = r.base.length) : completeRows r z = fullRows r z := by
  rw [completeRows, repairRows_eq_nil_of_full z hf, List.append_nil]
  simp only [liftRows, fullRows, fullBases, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro j hj
  exact liftRow_eq_fullAt z hf (List.mem_range.mp hj)

theorem shortPathAt_flatten_perm {r : Row α} (z : α) (hn : 2 ≤ r.base.length)
    (hs : r.visible = r.base.length - 2) :
    ((List.range (r.base.length - 1)).map (shortPathAt r z)).flatten.Perm (completeRows r z) := by
  have hlen : r.base.length - 1 = (r.base.length - 2) + 1 := by omega
  have hlen2 : r.base.length = (r.base.length - 2) + 1 + 1 := by omega
  have hmaps : (List.range (r.base.length - 2)).map (shortPathAt r z) =
      (List.range (r.base.length - 2)).map (fun j => [liftRow r z j]) := by
    apply List.map_congr_left
    intro j hj
    simp only [shortPathAt, if_pos (List.mem_range.mp hj)]
  have hflat : ((List.range (r.base.length - 1)).map (shortPathAt r z)).flatten =
      (List.range (r.base.length - 2)).map (liftRow r z) ++
        [liftRow r z (r.base.length - 2), repairRow r z (r.base.length - 2),
          repairRow r z (r.base.length - 1), liftRow r z (r.base.length - 1)] := by
    rw [hlen, List.range_succ, List.map_append, List.flatten_append, hmaps,
      flatten_map_singletons]
    simp [shortPathAt, ← hlen]
  have hrange : List.range r.base.length =
      List.range (r.base.length - 2) ++ [r.base.length - 2, r.base.length - 1] := by
    calc
      List.range r.base.length = List.range ((r.base.length - 2) + 1 + 1) := congrArg List.range hlen2
      _ = _ := by
        rw [List.range_succ, List.range_succ]
        simp only [List.append_assoc, List.singleton_append, hlen]
  have hrepair : repairRows r z =
      [repairRow r z (r.base.length - 2), repairRow r z (r.base.length - 1)] := by
    simp only [repairRows, hs, show r.base.length - (r.base.length - 2) = 2 by omega]
    simp [List.range'_succ, ← hlen]
  rw [hflat, completeRows, liftRows, hrange, hrepair, List.map_append,
    List.map_cons, List.map_cons, List.map_nil, List.append_assoc]
  apply List.Perm.append_left
  apply List.Perm.cons
  exact List.perm_append_comm (l₁ := [repairRow r z (r.base.length - 2),
    repairRow r z (r.base.length - 1)]) (l₂ := [liftRow r z (r.base.length - 1)])

/-- Every literal completion row occurrence appears once in the indexed paths. -/
theorem portPaths_flatten_perm {r : Row α} (z : α) (hn : 2 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((List.range (r.base.length - 1)).map (portPath r z)).flatten.Perm (completeRows r z) := by
  change ((List.range (r.base.length - 1)).map (fun j => portPath r z j)).flatten.Perm _
  by_cases hf : r.visible = r.base.length
  · simp only [portPath, if_pos hf]
    rw [Transport.map_fullPathAt_eq_fullPaths r z hn, completeRows_eq_fullRows z hf]
    exact Transport.fullPaths_flatten_perm r z hn
  · simp only [portPath, if_neg hf]
    exact shortPathAt_flatten_perm z hn (hkind.resolve_left hf)

end SuperpermutationUpperBound.Completion

#print axioms SuperpermutationUpperBound.Completion.short_exceptional_endpoints
#print axioms SuperpermutationUpperBound.Completion.portPath_internal
#print axioms SuperpermutationUpperBound.Completion.portPath_endpoints
#print axioms SuperpermutationUpperBound.Completion.portPaths_flatten_perm
