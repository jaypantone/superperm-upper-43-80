import SuperpermutationUpperBound.Transport.Local

/-!
Local completion: the new rows and their return chains. This file proves
validity, exact accounting and literal repair endpoints. Coverage of all
final cyclic classes is proved separately.
-/

namespace SuperpermutationUpperBound.Completion

variable {α : Type}

def liftRow (r : Row α) (z : α) (j : Nat) : Row α :=
  ⟨Transport.insertLetter r.base z j, r.satellite,
    r.visible + if j < r.visible then 1 else 0⟩

def repairRow (r : Row α) (z : α) (j : Nat) : Row α :=
  ⟨rot r.base j ++ [r.satellite], z, r.base.length + 1⟩

def liftRows (r : Row α) (z : α) : List (Row α) :=
  (List.range r.base.length).map (liftRow r z)

def repairRows (r : Row α) (z : α) : List (Row α) :=
  (List.range' r.visible (r.base.length - r.visible)).map (repairRow r z)

def completeRows (r : Row α) (z : α) : List (Row α) :=
  liftRows r z ++ repairRows r z

@[simp] theorem liftRow_base_length (r : Row α) (z : α) (j : Nat) :
    (liftRow r z j).base.length = r.base.length + 1 := by
  simp [liftRow]

@[simp] theorem repairRow_base_length (r : Row α) (z : α) (j : Nat) :
    (repairRow r z j).base.length = r.base.length + 1 := by
  simp [repairRow]

theorem liftRow_valid {r : Row α} (hr : r.Valid) {z : α}
    (hz : z ∉ r.base) (hzs : z ≠ r.satellite) (j : Nat) : (liftRow r z j).Valid := by
  refine ⟨Transport.insertLetter_nodup hr.1 hz j,
    Transport.insertLetter_fresh hr.2.1 (Ne.symm hzs) j, ?_, ?_⟩
  · dsimp [liftRow]
    have := hr.2.2.1
    split <;> omega
  · change r.visible + (if j < r.visible then 1 else 0) ≤ _
    rw [liftRow_base_length]
    have := hr.2.2.2
    split <;> omega

theorem repairRow_valid {r : Row α} (hr : r.Valid) {z : α}
    (hz : z ∉ r.base) (hzs : z ≠ r.satellite) (j : Nat) : (repairRow r z j).Valid := by
  have hs : r.satellite ∉ rot r.base j :=
    fun hm => hr.2.1 ((rot_perm r.base j).mem_iff.mp hm)
  have hz' : z ∉ rot r.base j :=
    fun hm => hz ((rot_perm r.base j).mem_iff.mp hm)
  refine ⟨?_, ?_, by simp [repairRow], ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨rot_nodup hr.1 j, by simp, ?_⟩
    intro a ha b hb he
    have hb' : b = r.satellite := List.mem_singleton.mp hb
    subst b
    subst a
    exact hs ha
  · simpa [repairRow, List.mem_append, List.mem_singleton] using And.intro hz' hzs
  · exact Nat.le_of_eq (repairRow_base_length r z j).symm

theorem completeRows_valid {r : Row α} (hr : r.Valid) {z : α}
    (hz : z ∉ r.base) (hzs : z ≠ r.satellite) :
    ∀ t ∈ completeRows r z, t.Valid ∧ t.base.length = r.base.length + 1 := by
  intro t ht
  rcases List.mem_append.mp ht with hl | hrp
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
    exact ⟨liftRow_valid hr hz hzs j, liftRow_base_length r z j⟩
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hrp
    exact ⟨repairRow_valid hr hz hzs j, repairRow_base_length r z j⟩

@[simp] theorem liftRows_length (r : Row α) (z : α) :
    (liftRows r z).length = r.base.length := by simp [liftRows]

@[simp] theorem repairRows_length (r : Row α) (z : α) :
    (repairRows r z).length = r.base.length - r.visible := by simp [repairRows]

@[simp] theorem completeRows_length (r : Row α) (z : α) :
    (completeRows r z).length = r.base.length + (r.base.length - r.visible) := by
  simp [completeRows]

theorem repairRows_eq_nil_of_full {r : Row α} (z : α)
    (hfull : r.visible = r.base.length) : repairRows r z = [] := by
  simp [repairRows, hfull]

private theorem sum_map_constant {β : Type} (xs : List β) (f : β → Nat) (c : Nat)
    (h : ∀ x ∈ xs, f x = c) : (xs.map f).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [h x (by simp), ih (by intro y hy; exact h y (List.mem_cons_of_mem _ hy))]
      rw [Nat.succ_mul, Nat.add_comm]

private theorem sum_map_range_split (f : Nat → Nat) {n L a b : Nat} (hL : L ≤ n)
    (ha : ∀ j, j < L → f j = a) (hb : ∀ j, L ≤ j → j < n → f j = b) :
    ((List.range n).map f).sum = L * a + (n - L) * b := by
  have hsplit : List.range n = List.range L ++ List.range' L (n - L) := by
    have h := List.range'_append_1 (s := 0) (m := L) (n := n - L)
    simpa only [Nat.zero_add, Nat.add_sub_of_le hL, ← List.range_eq_range'] using h.symm
  rw [hsplit, List.map_append, List.sum_append]
  rw [sum_map_constant _ f a (fun j hj => ha j (List.mem_range.mp hj))]
  rw [sum_map_constant _ f b (by
    intro j hj
    have hj' := List.mem_range'_1.mp hj
    exact hb j hj'.1 (by omega))]
  simp

theorem liftRows_visible_sum {r : Row α} (hr : r.Valid) (z : α) :
    ((liftRows r z).map Row.visible).sum = (r.base.length + 1) * r.visible := by
  have hs := sum_map_range_split (fun j => (liftRow r z j).visible) hr.2.2.2
    (a := r.visible + 1) (b := r.visible)
    (by intro j hj; simp [liftRow, hj])
    (by intro j hj _; simp [liftRow, Nat.not_lt.mpr hj])
  have he : r.visible + (r.base.length - r.visible) = r.base.length :=
    Nat.add_sub_of_le hr.2.2.2
  have hm := congrArg (fun n => n * r.visible) he
  simp only [Nat.add_mul] at hm
  change (((List.range r.base.length).map (liftRow r z)).map Row.visible).sum = _
  simp only [List.map_map, Function.comp_def]
  rw [hs, Nat.mul_succ, Nat.succ_mul]
  omega

theorem repairRows_visible_sum (r : Row α) (z : α) :
    ((repairRows r z).map Row.visible).sum =
      (r.base.length + 1) * (r.base.length - r.visible) := by
  have hs := sum_map_constant (repairRows r z) Row.visible (r.base.length + 1) (by
    intro t ht
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
    rfl)
  simpa only [repairRows_length, Nat.mul_comm] using hs

theorem completeRows_visible_sum {r : Row α} (hr : r.Valid) (z : α) :
    ((completeRows r z).map Row.visible).sum = r.base.length * (r.base.length + 1) := by
  rw [completeRows, List.map_append, List.sum_append, liftRows_visible_sum hr,
    repairRows_visible_sum, ← Nat.mul_add, Nat.add_sub_of_le hr.2.2.2, Nat.mul_comm]

theorem liftRows_charge_sum {r : Row α} (hr : r.Valid) (z : α) :
    ((liftRows r z).map Row.charge).sum =
      (r.base.length + 1) * (r.base.length - r.visible) := by
  have hs := sum_map_range_split (fun j => (liftRow r z j).charge) hr.2.2.2
    (a := r.base.length - r.visible) (b := r.base.length - r.visible + 1)
    (by intro j hj; simp [Row.charge, liftRow, hj])
    (by
      intro j hj _
      simp only [Row.charge, liftRow, Transport.insertLetter_length, if_neg (Nat.not_lt.mpr hj),
        Nat.add_zero]
      have := hr.2.2.2
      omega)
  change (((List.range r.base.length).map (liftRow r z)).map Row.charge).sum = _
  simp only [List.map_map, Function.comp_def]
  rw [hs, Nat.mul_succ, ← Nat.add_assoc, ← Nat.add_mul,
    Nat.add_sub_of_le hr.2.2.2, Nat.succ_mul]

@[simp] theorem repairRow_charge (r : Row α) (z : α) (j : Nat) :
    (repairRow r z j).charge = 0 := by simp [Row.charge, repairRow]

theorem repairRows_charge_sum (r : Row α) (z : α) :
    ((repairRows r z).map Row.charge).sum = 0 := by
  have hs := sum_map_constant (repairRows r z) Row.charge 0 (by
    intro t ht
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
    exact repairRow_charge r z j)
  simpa only [Nat.mul_zero] using hs

theorem completeRows_charge_sum {r : Row α} (hr : r.Valid) (z : α) :
    ((completeRows r z).map Row.charge).sum =
      (r.base.length + 1) * (r.base.length - r.visible) := by
  rw [completeRows, List.map_append, List.sum_append, liftRows_charge_sum hr,
    repairRows_charge_sum, Nat.add_zero]

theorem repairRow_head (r : Row α) (z : α) (j : Nat) :
    (repairRow r z j).head = (rot r.base j).take (r.base.length - 1) := by
  simp only [Row.head, repairRow, List.length_append, rot_length, List.length_singleton]
  have he : r.base.length + 1 - 2 = r.base.length - 1 := by omega
  rw [he, List.take_append_of_le_length (by simp)]

private theorem take_rot_append_singleton (x : List α) (s : α) (hn : 1 ≤ x.length) :
    (rot (x ++ [s]) 1).take (x.length - 1) = (rot x 1).take (x.length - 1) := by
  rw [take_rot_eq_drop x 1 hn]
  rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
  rw [List.drop_append_of_le_length hn, List.take_append_of_le_length hn]
  have he : x.length - 1 = (x.drop 1).length := (List.length_drop ..).symm
  rw [he, List.append_assoc, List.take_append_length]

theorem repairRow_tail (r : Row α) (z : α) (j : Nat) (hn : 1 ≤ r.base.length) :
    (repairRow r z j).tail = (rot r.base (j + 1)).take (r.base.length - 1) := by
  change (rot (rot r.base j ++ [r.satellite]) (r.base.length + 1 + 1)).take
    ((rot r.base j ++ [r.satellite]).length - 2) = _
  have hlen : (rot r.base j ++ [r.satellite]).length = r.base.length + 1 := by simp
  have hstep : r.base.length + 1 + 1 = 1 + (rot r.base j ++ [r.satellite]).length := by
    rw [hlen]
    omega
  rw [hstep, rot_add_length, hlen]
  have he : r.base.length + 1 - 2 = r.base.length - 1 := by omega
  rw [he]
  have ht := take_rot_append_singleton (rot r.base j) r.satellite (by simpa using hn)
  simpa only [rot_length, rot_add] using ht

/-- Repair rows at consecutive omitted gaps meet on equal literal tuples. -/
theorem repairRow_compatible_next (r : Row α) (z : α) (j : Nat)
    (hn : 1 ≤ r.base.length) :
    Row.Compatible (repairRow r z j) (repairRow r z (j + 1)) := by
  unfold Row.Compatible
  rw [repairRow_tail r z j hn, repairRow_head]

theorem repairRow_final_tail (r : Row α) (z : α) (hn : 1 ≤ r.base.length) :
    (repairRow r z (r.base.length - 1)).tail = r.base.take (r.base.length - 1) := by
  rw [repairRow_tail r z _ hn]
  have he : r.base.length - 1 + 1 = r.base.length := by omega
  rw [he, rot_length_self]

theorem full_exceptional_endpoints_agree {r : Row α}
    (hfull : r.visible = r.base.length) :
    (rot r.base r.visible).take (r.base.length - 1) = r.base.take (r.base.length - 1) := by
  rw [hfull, rot_length_self]

/-- All count and charge claims refer to the actual selected local rows. -/
theorem completeRows_local_certificate {r : Row α} (hr : r.Valid) {z : α}
    (hz : z ∉ r.base) (hzs : z ≠ r.satellite) :
    (liftRows r z).length = r.base.length ∧
    (repairRows r z).length = r.base.length - r.visible ∧
    (completeRows r z).length = r.base.length + (r.base.length - r.visible) ∧
    (∀ t ∈ completeRows r z, t.Valid ∧ t.base.length = r.base.length + 1) ∧
    ((liftRows r z).map Row.visible).sum = (r.base.length + 1) * r.visible ∧
    ((repairRows r z).map Row.visible).sum =
      (r.base.length + 1) * (r.base.length - r.visible) ∧
    ((completeRows r z).map Row.visible).sum = r.base.length * (r.base.length + 1) ∧
    ((completeRows r z).map Row.charge).sum =
      (r.base.length + 1) * (r.base.length - r.visible) :=
  ⟨liftRows_length r z, repairRows_length r z, completeRows_length r z,
    completeRows_valid hr hz hzs, liftRows_visible_sum hr z, repairRows_visible_sum r z,
    completeRows_visible_sum hr z, completeRows_charge_sum hr z⟩

end SuperpermutationUpperBound.Completion
