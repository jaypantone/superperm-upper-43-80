import SuperpermutationUpperBound.Completion.Local
import SuperpermutationUpperBound.Partition.AllSizes

/-! Exact completion counts for an entire row family. Literal coverage of all
classes requires the separate completion projection theorem; equality of the
visible sum with a factorial is not used as a substitute for that theorem. -/
namespace SuperpermutationUpperBound.Completion

variable {α : Type}

def packingRows (rs : List (Row α)) (z : α) : List (Row α) :=
  rs.flatMap (fun r => completeRows r z)

theorem packingRows_length {rs : List (Row α)} (z : α) (n : Nat)
    (hr : ∀ r ∈ rs, r.Valid ∧ r.base.length = n) :
    (packingRows rs z).length = n * rs.length + (rs.map Row.charge).sum := by
  induction rs with
  | nil => simp [packingRows]
  | cons r rs ih =>
    have h := hr r (by simp)
    have ht := ih (fun t ht => hr t (List.mem_cons_of_mem _ ht))
    change (completeRows r z ++ packingRows rs z).length = _
    rw [List.length_append, completeRows_length, h.2, ht]
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ]
    have hc : r.charge = n - r.visible := by simp only [Row.charge, h.2]
    omega

theorem packingRows_charge_sum {rs : List (Row α)} (z : α) (n : Nat)
    (hr : ∀ r ∈ rs, r.Valid ∧ r.base.length = n) :
    ((packingRows rs z).map Row.charge).sum = (n + 1) * (rs.map Row.charge).sum := by
  induction rs with
  | nil => simp [packingRows]
  | cons r rs ih =>
    have h := hr r (by simp)
    have ht := ih (fun t ht => hr t (List.mem_cons_of_mem _ ht))
    change ((completeRows r z ++ packingRows rs z).map Row.charge).sum = _
    rw [List.map_append, List.sum_append, completeRows_charge_sum h.1, h.2, ht]
    simp [Nat.mul_add, Row.charge, h.2]

theorem packingRows_visible_sum {rs : List (Row α)} (z : α) (n : Nat)
    (hr : ∀ r ∈ rs, r.Valid ∧ r.base.length = n) :
    ((packingRows rs z).map Row.visible).sum = n * (n + 1) * rs.length := by
  induction rs with
  | nil => simp [packingRows]
  | cons r rs ih =>
    have h := hr r (by simp)
    have ht := ih (fun t ht => hr t (List.mem_cons_of_mem _ ht))
    change ((completeRows r z ++ packingRows rs z).map Row.visible).sum = _
    rw [List.map_append, List.sum_append, completeRows_visible_sum h.1, h.2, ht]
    simp only [List.length_cons, Nat.mul_succ]
    omega

theorem packingRows_valid {alphabet : List α} {s z : α} {rs : List (Row α)}
    (hb : BasedOn alphabet s rs) (hz : z ∉ alphabet) (hzs : z ≠ s) :
    ∀ t ∈ packingRows rs z, t.Valid ∧ t.base.length = alphabet.length + 1 := by
  intro t ht
  obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp ht
  have h := (hb.ready hz hzs) r hr
  have hv := completeRows_valid h.1.1 h.1.2.1 h.1.2.2.1 t ht
  refine ⟨hv.1, ?_⟩
  have hl := hv.2
  omega

/-- The completed all-size family has the paper's factorial row and charge
counts. This theorem asserts counts and row validity, not global coverage. -/
theorem original_family_counts (k : Nat) :
    (packingRows (Partition.blockRows k) (k + 8)).length =
      Nat.factorial (k + 7) + ((Partition.blockRows k).map Row.charge).sum ∧
    ((packingRows (Partition.blockRows k) (k + 8)).map Row.charge).sum =
      (k + 8) * ((Partition.blockRows k).map Row.charge).sum ∧
    ((packingRows (Partition.blockRows k) (k + 8)).map Row.visible).sum =
      Nat.factorial (k + 8) ∧
    (∀ t ∈ packingRows (Partition.blockRows k) (k + 8), t.Valid ∧ t.base.length = k + 8) := by
  have hb := Partition.blockRows_basedOn k
  have hz := Partition.blockAlphabet_fresh k
  have hr : ∀ r ∈ Partition.blockRows k, r.Valid ∧ r.base.length = k + 7 := by
    intro r hr
    exact ⟨(hb r hr).1, (hb r hr).2.1.length_eq.trans (Partition.blockAlphabet_length k)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [packingRows_length _ _ hr, Partition.blockRows_length]
    have hf : Nat.factorial (k + 7) = (k + 7) * Nat.factorial (k + 6) :=
      Nat.factorial_succ (k + 6)
    rw [hf]
  · simpa using packingRows_charge_sum (k + 8) (k + 7) hr
  · rw [packingRows_visible_sum _ _ hr, Partition.blockRows_length]
    have hf : Nat.factorial (k + 7) = (k + 7) * Nat.factorial (k + 6) :=
      Nat.factorial_succ (k + 6)
    have hf' : Nat.factorial (k + 8) = (k + 8) * Nat.factorial (k + 7) :=
      Nat.factorial_succ (k + 7)
    rw [hf', hf]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · simpa [Partition.blockAlphabet_length] using packingRows_valid hb hz (by omega)

end SuperpermutationUpperBound.Completion
