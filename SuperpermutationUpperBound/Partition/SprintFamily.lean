import SuperpermutationUpperBound.Partition.SprintBase
import SuperpermutationUpperBound.Completion.Counts
import SuperpermutationUpperBound.Completion.Alphabet

namespace SuperpermutationUpperBound.Partition.SprintFamily

/-- Reserve 9 and 10 as satellite and completion letters. Subsequent ordinary
letters are 11, 12,..., so the full word alphabet stays an initial Nat interval. -/
def alphabet : Nat → List Nat
  | 0 => SprintBase.alphabet9
  | k + 1 => (k + 11) :: alphabet k

def rows : Nat → List (Row Nat)
  | 0 => SprintBase.rows9
  | k + 1 => Transport.packingRows (rows k) (k + 11)

@[simp] theorem alphabet_length (k : Nat) : (alphabet k).length = k + 9 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [alphabet, ih, Nat.add_assoc]

theorem alphabet_lt (k : Nat) : ∀ a ∈ alphabet k, a < k + 11 := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih a ha; omega

theorem alphabet_fresh (k : Nat) : k + 11 ∉ alphabet k := by
  intro h
  have := alphabet_lt k (k + 11) h
  omega

theorem alphabet_nodup (k : Nat) : (alphabet k).Nodup := by
  induction k with
  | zero => decide
  | succ k ih => exact List.nodup_cons.mpr ⟨alphabet_fresh k, ih⟩

theorem alphabet_satellite (k : Nat) : 9 ∉ alphabet k := by
  induction k with
  | zero => decide
  | succ k ih => simpa [alphabet] using And.intro (by omega : 9 ≠ k + 11) ih

theorem alphabet_final (k : Nat) : 10 ∉ alphabet k := by
  induction k with
  | zero => decide
  | succ k ih => simpa [alphabet] using And.intro (by omega : 10 ≠ k + 11) ih

theorem alphabet_nonempty (k : Nat) : alphabet k ≠ [] := by
  have h := alphabet_length k
  intro he
  rw [he] at h
  simp at h

theorem rows_basedOn (k : Nat) : BasedOn (alphabet k) 9 (rows k) := by
  induction k with
  | zero => exact SprintBase.rows9_basedOn
  | succ k ih => exact ih.transport (alphabet_fresh k) (by omega)

theorem rows_complete (k : Nat) : BlockComplete (alphabet k) (rows k) := by
  induction k with
  | zero => exact SprintBase.rows9_complete
  | succ k ih =>
    exact ih.transport (rows_basedOn k) (alphabet_nodup k)
      (alphabet_nonempty k) (alphabet_fresh k)

theorem rows_length (k : Nat) : (rows k).length = (k + 8).factorial := by
  induction k with
  | zero => exact SprintBase.rows9_counts.1
  | succ k ih =>
    have hc := Transport.packingRows_length (rows k) (k + 11) (alphabet k).length
      ((rows_basedOn k).ready (alphabet_fresh k) (by omega))
    change (Transport.packingRows (rows k) (k + 11)).length = _
    rw [hc, alphabet_length, ih]
    exact (Nat.factorial_succ (k + 8)).symm

theorem rows_chargeRatio (k : Nat) : ChargeRatio 7 15 (rows k) := by
  induction k with
  | zero =>
    change ChargeRatio 7 15 SprintBase.rows9
    unfold ChargeRatio
    rw [SprintBase.rows9_counts.1, SprintBase.rows9_counts.2]
  | succ k ih => exact chargeRatio_transport (rows_basedOn k) (alphabet_fresh k) (by omega) ih

theorem rows_charge (k : Nat) : 15 * ((rows k).map Row.charge).sum = 7 * (k + 8).factorial := by
  simpa only [ChargeRatio, rows_length] using rows_chargeRatio k

/-- The entire alphabet, including the fixed satellite and final letter,
contains exactly the symbols 0,...,k+10. -/
theorem full_alphabet_perm (k : Nat) : (10 :: (alphabet k ++ [9])).Perm (List.range (k + 11)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hswap : (10 :: ((k + 11) :: alphabet k ++ [9])).Perm
        ((k + 11) :: 10 :: (alphabet k ++ [9])) := List.Perm.swap ..
    change (10 :: ((k + 11) :: alphabet k ++ [9])).Perm _
    apply (hswap.trans (ih.cons (k + 11))).trans
    rw [show k + 1 + 11 = (k + 11) + 1 by omega, List.range_succ (n := k + 11)]
    exact List.perm_append_comm (l₁ := [k + 11]) (l₂ := List.range (k + 11))

end SuperpermutationUpperBound.Partition.SprintFamily

namespace SuperpermutationUpperBound.Partition.SprintFamily

def completedRows (k : Nat) : List (Row Nat) := Completion.packingRows (rows k) 10

/-- Exact row and visible counts after completion of the current historical
family; coverage is proved separately below. -/
theorem completedRows_counts (k : Nat) :
    (completedRows k).length = (k + 9).factorial + ((rows k).map Row.charge).sum ∧
    ((completedRows k).map Row.visible).sum = (k + 10).factorial ∧
    ∀ r ∈ completedRows k, r.Valid ∧ r.base.length = k + 10 := by
  have hr : ∀ r ∈ rows k, r.Valid ∧ r.base.length = k + 9 := by
    intro r hr
    exact ⟨(rows_basedOn k r hr).1, (rows_basedOn k r hr).2.1.length_eq.trans (alphabet_length k)⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [completedRows, Completion.packingRows_length _ _ hr, rows_length,
      show (k + 9).factorial = (k + 9) * (k + 8).factorial from Nat.factorial_succ (k + 8)]
  · rw [completedRows, Completion.packingRows_visible_sum _ _ hr, rows_length,
      show (k + 10).factorial = (k + 10) * (k + 9).factorial from Nat.factorial_succ (k + 9),
      show (k + 9).factorial = (k + 9) * (k + 8).factorial from Nat.factorial_succ (k + 8)]
    ring
  · simpa only [completedRows, alphabet_length, show k + 9 + 1 = k + 10 by omega] using
      Completion.packingRows_valid (rows_basedOn k) (alphabet_final k) (by decide : 10 ≠ 9)

end SuperpermutationUpperBound.Partition.SprintFamily

namespace SuperpermutationUpperBound.Partition.SprintFamily

theorem completedRows_cover_range (k : Nat) {p : List Nat}
    (hp : p.Perm (List.range (k + 11))) : ∃ r ∈ completedRows k, r.Assigned p :=
  Completion.packingRows_cover (rows_basedOn k) (rows_complete k)
    (alphabet_nodup k) (alphabet_nonempty k) (alphabet_satellite k) (alphabet_final k)
    (by decide) (hp.trans (full_alphabet_perm k).symm)

theorem completedRows_word_support (k : Nat) {r : Row Nat} (hr : r ∈ completedRows k) :
    ∀ a ∈ r.word, a < k + 11 := by
  intro a ha
  apply List.mem_range.mp
  exact (full_alphabet_perm k).mem_iff.mp
    (Completion.packingRows_word_mem (rows_basedOn k) hr ha)

end SuperpermutationUpperBound.Partition.SprintFamily
