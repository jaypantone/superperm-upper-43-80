import SuperpermutationUpperBound.Transport.Paths

/-! Local paths indexed by their input insertion ports. -/
namespace SuperpermutationUpperBound.Transport

variable {α : Type}

def fullPathAt (r : Row α) (z : α) (j : Nat) : List (Row α) :=
  if j = 0 then [fullAt r z 0, fullAt r z (r.base.length - 1)] else [fullAt r z j]

def shortPathAt (r : Row α) (z : α) (j : Nat) : List (Row α) :=
  if j < r.base.length - 2 then [shortAt r z j]
  else [shortAt r z (r.base.length - 2), shortLast r z]

def portPath (r : Row α) (z : α) (j : Nat) : List (Row α) :=
  if r.visible = r.base.length then fullPathAt r z j else shortPathAt r z j

def portTarget (r : Row α) (j : Nat) : Nat :=
  if r.visible = r.base.length then
    (j + (r.base.length - 2)) % (r.base.length - 1)
  else (j + 1) % (r.base.length - 1)

theorem fullPathAt_nonempty (r : Row α) (z : α) (j : Nat) : fullPathAt r z j ≠ [] := by
  unfold fullPathAt
  split <;> simp

theorem shortPathAt_nonempty (r : Row α) (z : α) (j : Nat) : shortPathAt r z j ≠ [] := by
  unfold shortPathAt
  split <;> simp

theorem portPath_nonempty (r : Row α) (z : α) (j : Nat) : portPath r z j ≠ [] := by
  unfold portPath
  split
  · exact fullPathAt_nonempty r z j
  · exact shortPathAt_nonempty r z j

theorem portTarget_full_zero {r : Row α} (hn : 3 ≤ r.base.length)
    (hf : r.visible = r.base.length) : portTarget r 0 = r.base.length - 2 := by
  simp only [portTarget, if_pos hf, Nat.zero_add]
  exact Nat.mod_eq_of_lt (by omega)

theorem portTarget_full_pos {r : Row α} {j : Nat} (hn : 3 ≤ r.base.length)
    (hf : r.visible = r.base.length) (hj : j < r.base.length - 1) (hjpos : 0 < j) :
    portTarget r j = j - 1 := by
  simp only [portTarget, if_pos hf]
  have heq : j + (r.base.length - 2) = (j - 1) + (r.base.length - 1) := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem portTarget_short_singleton {r : Row α} {j : Nat}
    (hf : r.visible ≠ r.base.length) (hj : j < r.base.length - 2) : portTarget r j = j + 1 := by
  simp only [portTarget, if_neg hf]
  exact Nat.mod_eq_of_lt (by omega)

theorem portTarget_short_final {r : Row α} (hn : 3 ≤ r.base.length)
    (hf : r.visible ≠ r.base.length) : portTarget r (r.base.length - 2) = 0 := by
  simp only [portTarget, if_neg hf]
  have heq : r.base.length - 2 + 1 = r.base.length - 1 := by omega
  rw [heq, Nat.mod_self]

theorem portTarget_lt {r : Row α} (hn : 3 ≤ r.base.length) (j : Nat) :
    portTarget r j < r.base.length - 1 := by
  unfold portTarget
  split <;> exact Nat.mod_lt _ (by omega)

theorem fullPathAt_internal (r : Row α) (z : α) (j : Nat) (hn : 2 ≤ r.base.length) :
    RowTrailCompatible ((fullPathAt r z j).head (fullPathAt_nonempty r z j))
      (fullPathAt r z j).tail := by
  by_cases hj : j = 0
  · simp only [fullPathAt, if_pos hj, List.head_cons, List.tail_cons, RowTrailCompatible]
    exact ⟨fullAt_exceptional_compatible r z hn, True.intro⟩
  · simp only [fullPathAt, if_neg hj, List.head_cons, List.tail_cons, RowTrailCompatible]

theorem shortPathAt_internal (r : Row α) (z : α) (j : Nat) (hn : 2 ≤ r.base.length) :
    RowTrailCompatible ((shortPathAt r z j).head (shortPathAt_nonempty r z j))
      (shortPathAt r z j).tail := by
  by_cases hj : j < r.base.length - 2
  · simp only [shortPathAt, if_pos hj, List.head_cons, List.tail_cons, RowTrailCompatible]
  · simp only [shortPathAt, if_neg hj, List.head_cons, List.tail_cons, RowTrailCompatible]
    exact ⟨shortAt_exceptional_compatible r z hn, True.intro⟩

theorem portPath_internal (r : Row α) (z : α) (j : Nat) (hn : 2 ≤ r.base.length) :
    RowTrailCompatible ((portPath r z j).head (portPath_nonempty r z j))
      (portPath r z j).tail := by
  by_cases hf : r.visible = r.base.length
  · simpa only [portPath, if_pos hf] using fullPathAt_internal r z j hn
  · simpa only [portPath, if_neg hf] using shortPathAt_internal r z j hn

theorem fullPathAt_endpoints {r : Row α} (z : α) {j : Nat} (hn : 3 ≤ r.base.length)
    (hf : r.visible = r.base.length) (hj : j < r.base.length - 1) :
    ((fullPathAt r z j).head?).map Row.head = some (insertLetter r.head z j) ∧
      ((fullPathAt r z j).getLast?).map Row.tail = some (insertLetter r.tail z (portTarget r j)) := by
  by_cases hjzero : j = 0
  · subst j
    have he := fullAt_exceptional_endpoints r z (by omega) hf
    constructor
    · simpa [fullPathAt] using congrArg some he.1
    · simpa [fullPathAt, portTarget_full_zero hn hf] using congrArg some he.2.2
  · have he := fullAt_singleton_endpoints r z j (by omega) hf (by omega) (by omega)
    constructor
    · simpa [fullPathAt, hjzero] using congrArg some he.1
    · simpa [fullPathAt, hjzero, portTarget_full_pos hn hf hj (by omega)] using congrArg some he.2

theorem shortPathAt_endpoints {r : Row α} (z : α) {j : Nat} (hn : 3 ≤ r.base.length)
    (hs : r.visible = r.base.length - 2) (hj : j < r.base.length - 1) :
    ((shortPathAt r z j).head?).map Row.head = some (insertLetter r.head z j) ∧
      ((shortPathAt r z j).getLast?).map Row.tail = some (insertLetter r.tail z (portTarget r j)) := by
  have hf : r.visible ≠ r.base.length := by omega
  by_cases hjshort : j < r.base.length - 2
  · have he := shortAt_singleton_endpoints r z j hn hs hjshort
    constructor
    · simpa [shortPathAt, hjshort] using congrArg some he.1
    · simpa [shortPathAt, hjshort, portTarget_short_singleton hf hjshort] using congrArg some he.2
  · have hjlast : j = r.base.length - 2 := by omega
    subst j
    have he := shortAt_exceptional_endpoints r z hn hs
    constructor
    · simpa [shortPathAt] using congrArg some he.1
    · simpa [shortPathAt, portTarget_short_final hn hf] using congrArg some he.2.2

/-- Both literal endpoint tuples agree with the input/output port indexing. -/
theorem portPath_endpoints {r : Row α} (z : α) {j : Nat} (hn : 3 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hj : j < r.base.length - 1) :
    ((portPath r z j).head?).map Row.head = some (insertLetter r.head z j) ∧
      ((portPath r z j).getLast?).map Row.tail = some (insertLetter r.tail z (portTarget r j)) := by
  by_cases hf : r.visible = r.base.length
  · simpa only [portPath, if_pos hf] using fullPathAt_endpoints z hn hf hj
  · simpa only [portPath, if_neg hf] using shortPathAt_endpoints z hn (hkind.resolve_left hf) hj

theorem map_fullPathAt_eq_fullPaths (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (List.range (r.base.length - 1)).map (fullPathAt r z) = fullPaths r z := by
  have hindex : List.range (r.base.length - 1) =
      0 :: List.range' 1 (r.base.length - 2) := by
    have hlen : r.base.length - 1 = (r.base.length - 2) + 1 := by omega
    rw [hlen, List.range_eq_range', List.range'_succ]
  have hmaps : (List.range' 1 (r.base.length - 2)).map (fullPathAt r z) =
      (List.range' 1 (r.base.length - 2)).map (fun j => [fullAt r z j]) := by
    apply List.map_congr_left
    intro j hj
    have hjpos : 0 < j := by have h := List.mem_range'_1.mp hj; omega
    simp only [fullPathAt, if_neg (by omega : j ≠ 0)]
  rw [hindex, List.map_cons, hmaps]
  rfl

theorem map_shortPathAt_eq_shortPaths (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (List.range (r.base.length - 1)).map (shortPathAt r z) = shortPaths r z := by
  have hmaps : (List.range (r.base.length - 2)).map (shortPathAt r z) =
      (List.range (r.base.length - 2)).map (fun j => [shortAt r z j]) := by
    apply List.map_congr_left
    intro j hj
    simp only [shortPathAt, if_pos (List.mem_range.mp hj)]
  have hlen : r.base.length - 1 = (r.base.length - 2) + 1 := by omega
  rw [hlen, List.range_succ, List.map_append, List.map_singleton, hmaps]
  simp only [shortPathAt, Nat.lt_irrefl, if_false, shortPaths]

/-- Input ports enumerate every literal replacement row occurrence exactly once. -/
theorem portPaths_flatten_perm (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    ((List.range (r.base.length - 1)).map (portPath r z)).flatten.Perm (rows r z) := by
  change ((List.range (r.base.length - 1)).map (fun j => portPath r z j)).flatten.Perm _
  by_cases hf : r.visible = r.base.length
  · simp only [portPath, rows, if_pos hf]
    rw [map_fullPathAt_eq_fullPaths r z hn]
    exact fullPaths_flatten_perm r z hn
  · simp only [portPath, rows, if_neg hf]
    rw [map_shortPathAt_eq_shortPaths r z hn, shortPaths_flatten r z hn]

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

end SuperpermutationUpperBound.Transport
