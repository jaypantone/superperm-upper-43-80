import SuperpermutationUpperBound.Partition.OriginalSeven
import SuperpermutationUpperBound.Partition.Iterated
import Mathlib.Data.Nat.Factorial.Basic

/-! A kernel-checked all-size family partitioning the cyclic base blocks, with
charge ratio two fifths. It starts from the actual size-seven row selection:
transported seed rows and the 24 closed full charts. This file proves block
coverage, distinctness and exact counts. Global mixed-component assembly and
its run invariant remain separate properties. -/
namespace SuperpermutationUpperBound.Partition

def blockAlphabet : Nat → List Nat
  | 0 => OriginalSeven.alphabet7
  | k + 1 => (k + 8) :: blockAlphabet k

def blockRows : Nat → List (Row Nat)
  | 0 => OriginalSeven.rows7
  | k + 1 => Transport.packingRows (blockRows k) (k + 8)

@[simp] theorem blockAlphabet_length (k : Nat) : (blockAlphabet k).length = k + 7 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [blockAlphabet, ih, Nat.add_assoc]

theorem blockAlphabet_lt (k : Nat) : ∀ a ∈ blockAlphabet k, a < k + 8 := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih a ha
      omega

theorem blockAlphabet_fresh (k : Nat) : k + 8 ∉ blockAlphabet k := by
  intro h
  have := blockAlphabet_lt k (k + 8) h
  omega

theorem blockAlphabet_nodup (k : Nat) : (blockAlphabet k).Nodup := by
  induction k with
  | zero => decide
  | succ k ih => exact List.nodup_cons.mpr ⟨blockAlphabet_fresh k, ih⟩

theorem blockAlphabet_nonempty (k : Nat) : blockAlphabet k ≠ [] := by
  have h := blockAlphabet_length k
  intro he
  rw [he] at h
  simp at h

theorem blockRows_basedOn (k : Nat) : BasedOn (blockAlphabet k) 6 (blockRows k) := by
  induction k with
  | zero => exact OriginalSeven.rows7_basedOn
  | succ k ih => exact ih.transport (blockAlphabet_fresh k) (by omega)

theorem blockRows_complete (k : Nat) : BlockComplete (blockAlphabet k) (blockRows k) := by
  induction k with
  | zero => exact OriginalSeven.rows7_complete
  | succ k ih =>
    exact ih.transport (blockRows_basedOn k) (blockAlphabet_nodup k)
      (blockAlphabet_nonempty k) (blockAlphabet_fresh k)

theorem blockRows_distinct (k : Nat) : DistinctBlocks (blockRows k) := by
  induction k with
  | zero => exact OriginalSeven.rows7_distinct
  | succ k ih => exact ih.transport (blockRows_basedOn k) (blockAlphabet_fresh k)

theorem blockRows_length (k : Nat) : (blockRows k).length = Nat.factorial (k + 6) := by
  induction k with
  | zero => exact OriginalSeven.rows7_length
  | succ k ih =>
    have hc := Transport.packingRows_length (blockRows k) (k + 8) (blockAlphabet k).length
      ((blockRows_basedOn k).ready (blockAlphabet_fresh k) (by omega))
    change (Transport.packingRows (blockRows k) (k + 8)).length = _
    rw [hc, blockAlphabet_length, ih]
    exact (Nat.factorial_succ (k + 6)).symm

private theorem original_chargeRatio : ChargeRatio 2 5 OriginalSeven.rows7 := by
  unfold ChargeRatio
  rw [OriginalSeven.rows7_charge, OriginalSeven.rows7_length]

theorem blockRows_chargeRatio (k : Nat) : ChargeRatio 2 5 (blockRows k) := by
  induction k with
  | zero => exact original_chargeRatio
  | succ k ih =>
    exact chargeRatio_transport (blockRows_basedOn k) (blockAlphabet_fresh k) (by omega) ih

/-- An unconditional all-size cyclic-block partition with the original charge
ratio. It is not yet a theorem about the closed components or final words. -/
theorem blockRows_certificate (k : Nat) :
    (blockAlphabet k).length = k + 7 ∧
    BasedOn (blockAlphabet k) 6 (blockRows k) ∧
    BlockComplete (blockAlphabet k) (blockRows k) ∧ DistinctBlocks (blockRows k) ∧
    (blockRows k).length = Nat.factorial (k + 6) ∧
    5 * ((blockRows k).map Row.charge).sum = 2 * Nat.factorial (k + 6) := by
  refine ⟨blockAlphabet_length k, blockRows_basedOn k, blockRows_complete k,
    blockRows_distinct k, blockRows_length k, ?_⟩
  simpa only [ChargeRatio, blockRows_length] using blockRows_chargeRatio k

end SuperpermutationUpperBound.Partition
