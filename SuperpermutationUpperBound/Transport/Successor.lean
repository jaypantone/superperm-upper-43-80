import SuperpermutationUpperBound.Transport.IndexedPaths
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-! A bijective successor on labeled row-index/port states. -/
namespace SuperpermutationUpperBound.Transport

variable {ι : Type u} {π : Type v} {α : Type}

/-- Move the row label by σ and apply the port bijection belonging to the
source row label. The inverse recovers that source label first. -/
def skewPerm (σ : Equiv.Perm ι) (τ : ι → Equiv.Perm π) : Equiv.Perm (ι × π) where
  toFun ip := (σ ip.1, τ ip.1 ip.2)
  invFun ip := (σ.symm ip.1, (τ (σ.symm ip.1)).symm ip.2)
  left_inv ip := by rcases ip with ⟨i, p⟩; simp
  right_inv ip := by rcases ip with ⟨i, p⟩; simp

@[simp] theorem skewPerm_fst (σ : Equiv.Perm ι) (τ : ι → Equiv.Perm π) (ip : ι × π) :
    (skewPerm σ τ ip).1 = σ ip.1 := rfl

@[simp] theorem skewPerm_snd (σ : Equiv.Perm ι) (τ : ι → Equiv.Perm π) (ip : ι × π) :
    (skewPerm σ τ ip).2 = τ ip.1 ip.2 := rfl

/-- The next row occurrence, cyclically, including the one-row case. -/
def rowIndexPerm (R : Nat) (hR : 0 < R) : Equiv.Perm (Fin R) := by
  letI : NeZero R := ⟨by omega⟩
  exact Equiv.addRight 1

theorem rowIndexPerm_val (R : Nat) (hR : 0 < R) (i : Fin R) :
    (rowIndexPerm R hR i).val = (i.val + 1) % R := by
  simp [rowIndexPerm, Fin.val_add, Nat.add_mod_mod]

/-- Full rows translate ports by -1 and all other rows by +1. Its agreement
with geometric paths uses the full/deficit-two row hypothesis separately. -/
def portPerm (n : Nat) (hn : 3 ≤ n) (r : Row α) : Equiv.Perm (Fin (n - 1)) := by
  letI : NeZero (n - 1) := ⟨by omega⟩
  exact Equiv.addRight ⟨if r.visible = r.base.length then n - 2 else 1,
    by split <;> omega⟩

theorem portPerm_val_eq_portTarget (n : Nat) (hn : 3 ≤ n) (r : Row α)
    (hbase : r.base.length = n) (p : Fin (n - 1)) :
    (portPerm n hn r p).val = portTarget r p.val := by
  by_cases hf : r.visible = r.base.length
  · simp [portPerm, portTarget, hf, hbase, Fin.val_add]
  · have hfn : r.visible ≠ n := by simpa only [hbase] using hf
    simp [portPerm, portTarget, hfn, hbase, Fin.val_add]

/-- Uniform-size labeled row and port successor. -/
def rowPortSuccessor {R : Nat} (hR : 0 < R) (n : Nat) (hn : 3 ≤ n)
    (row : Fin R → Row α) : Equiv.Perm (Fin R × Fin (n - 1)) :=
  skewPerm (rowIndexPerm R hR) (fun i => portPerm n hn (row i))

@[simp] theorem rowPortSuccessor_fst {R : Nat} (hR : 0 < R) (n : Nat) (hn : 3 ≤ n)
    (row : Fin R → Row α) (ip : Fin R × Fin (n - 1)) :
    (rowPortSuccessor hR n hn row ip).1 = rowIndexPerm R hR ip.1 := rfl

@[simp] theorem rowPortSuccessor_snd {R : Nat} (hR : 0 < R) (n : Nat) (hn : 3 ≤ n)
    (row : Fin R → Row α) (ip : Fin R × Fin (n - 1)) :
    (rowPortSuccessor hR n hn row ip).2 = portPerm n hn (row ip.1) ip.2 := rfl

theorem rowPortSuccessor_fst_val {R : Nat} (hR : 0 < R) (n : Nat) (hn : 3 ≤ n)
    (row : Fin R → Row α) (ip : Fin R × Fin (n - 1)) :
    (rowPortSuccessor hR n hn row ip).1.val = (ip.1.val + 1) % R :=
  rowIndexPerm_val R hR ip.1

theorem rowPortSuccessor_snd_val {R : Nat} (hR : 0 < R) (n : Nat) (hn : 3 ≤ n)
    (row : Fin R → Row α) (hbase : ∀ i, (row i).base.length = n)
    (ip : Fin R × Fin (n - 1)) :
    (rowPortSuccessor hR n hn row ip).2.val = portTarget (row ip.1) ip.2.val :=
  portPerm_val_eq_portTarget n hn (row ip.1) (hbase ip.1) ip.2

end SuperpermutationUpperBound.Transport
