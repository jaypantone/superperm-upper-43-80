import SuperpermutationUpperBound.Transport.Successor
import SuperpermutationUpperBound.Transport.Monodromy
import SuperpermutationUpperBound.Transport.FiniteOrbits

/-! Iteration of the actual row/port successor over one complete old row lap. -/
namespace SuperpermutationUpperBound.Transport

variable {α : Type} {ι : Type}

theorem rowIndexPerm_iterate_val (R : Nat) (hR : 0 < R) (i : Fin R) (k : Nat) :
    (((rowIndexPerm R hR : Fin R → Fin R)^[k]) i).val = (i.val + k) % R := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', rowIndexPerm_val, ih, Nat.mod_add_mod]
    simp only [Nat.add_assoc]

theorem rowIndexPerm_full_lap (R : Nat) (hR : 0 < R) (i : Fin R) :
    ((rowIndexPerm R hR : Fin R → Fin R)^[R]) i = i := by
  apply Fin.ext
  rw [rowIndexPerm_iterate_val, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem rowIndexPerm_orbitLabels_zero (R : Nat) (hR : 0 < R) :
    orbitLabels (rowIndexPerm R hR) ⟨0, hR⟩ R = List.finRange R := by
  rw [orbitLabels_eq_map_iterate]
  apply List.ext_getElem (by simp)
  intro j hj hj'
  simp only [List.getElem_map, List.getElem_range]
  apply Fin.ext
  rw [rowIndexPerm_iterate_val]
  simp [Nat.mod_eq_of_lt (by simpa using hj : j < R)]

/-- Accumulate each source row's signed port displacement in occurrence order. -/
theorem skewPerm_iterate_shift (h : Nat) (σ : Equiv.Perm ι)
    (τ : ι → Equiv.Perm (Fin (h + 1))) (d : ι → Int)
    (hτ : ∀ i p, τ i p = shiftPort h (d i) p) (i : ι) (p : Fin (h + 1)) (k : Nat) :
    ((skewPerm σ τ : ι × Fin (h + 1) → ι × Fin (h + 1))^[k]) (i, p) =
      ((σ : ι → ι)^[k] i,
        shiftPort h ((orbitLabels σ i k).map d).sum p) := by
  induction k generalizing i p with
  | zero => simp [orbitLabels]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    change ((skewPerm σ τ : ι × Fin (h + 1) → ι × Fin (h + 1))^[k]) (σ i, τ i p) = _
    rw [ih, hτ, shiftPort_add]
    simp only [orbitLabels, List.map_cons, List.sum_cons, Function.iterate_succ_apply]

theorem skewPerm_full_lap_shift (R : Nat) (hR : 0 < R) (h : Nat)
    (τ : Fin R → Equiv.Perm (Fin (h + 1))) (d : Fin R → Int)
    (hτ : ∀ i p, τ i p = shiftPort h (d i) p) (p : Fin (h + 1)) :
    ((skewPerm (rowIndexPerm R hR) τ :
      Fin R × Fin (h + 1) → Fin R × Fin (h + 1))^[R]) (⟨0, hR⟩, p) =
      (⟨0, hR⟩, shiftPort h ((List.finRange R).map d).sum p) := by
  rw [skewPerm_iterate_shift h _ τ d hτ, rowIndexPerm_full_lap, rowIndexPerm_orbitLabels_zero]

theorem shiftPort_negative_one_val (h : Nat) (p : Fin (h + 1)) :
    (shiftPort h (-1) p).val = (p.val + h) % (h + 1) := by
  apply Int.ofNat_inj.mp
  rw [shiftPort_val, Int.natCast_emod]
  simp only [Int.natCast_add, Int.natCast_one]
  have heq : (p.val : Int) + (h : Int) =
      ((p.val : Int) + (-1)) + ((h : Int) + 1) := by omega
  rw [heq, Int.add_emod_right]

theorem shiftPort_one_val (h : Nat) (p : Fin (h + 1)) :
    (shiftPort h 1 p).val = (p.val + 1) % (h + 1) := by
  apply Int.ofNat_inj.mp
  rw [shiftPort_val, Int.natCast_emod]
  simp only [Int.natCast_add, Int.natCast_one]

/-- The geometric port permutation equals the signed ledger displacement. -/
theorem portPerm_eq_shiftPort_delta (h : Nat) (hn : 3 ≤ h + 2) (r : Row α)
    (hbase : r.base.length = h + 2)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (p : Fin (h + 1)) : portPerm (h + 2) hn r p = shiftPort h (delta r) p := by
  apply Fin.ext
  rw [portPerm_val_eq_portTarget (h + 2) hn r hbase p]
  rcases hkind with hf | hs
  · have hc : r.charge = 0 := by simp [Row.charge, hf]
    rw [delta_full hc, shiftPort_negative_one_val]
    simp [portTarget, hf, hbase]
  · have hc : r.charge = 2 := by unfold Row.charge; omega
    have hf : r.visible ≠ h + 2 := by omega
    rw [delta_short hc, shiftPort_one_val]
    simp [portTarget, hf, hbase]

/-- One full lap of the actual uniform-size row/port successor. -/
theorem rowPortSuccessor_full_lap {R : Nat} (hR : 0 < R) (h : Nat) (hn : 3 ≤ h + 2)
    (row : Fin R → Row α) (hbase : ∀ i, (row i).base.length = h + 2)
    (hkind : ∀ i, (row i).visible = (row i).base.length ∨
      (row i).visible = (row i).base.length - 2) (p : Fin (h + 1)) :
    ((rowPortSuccessor hR (h + 2) hn row :
      Fin R × Fin (h + 1) → Fin R × Fin (h + 1))^[R]) (⟨0, hR⟩, p) =
      (⟨0, hR⟩, shiftPort h ((List.finRange R).map (fun i => delta (row i))).sum p) := by
  exact skewPerm_full_lap_shift R hR h (fun i => portPerm (h + 2) hn (row i))
    (fun i => delta (row i)) (fun i p => portPerm_eq_shiftPort_delta h hn (row i)
      (hbase i) (hkind i) p) p

theorem finRange_map_list_getElem (rs : List (Row α)) :
    (List.finRange rs.length).map (fun i => rs[i.val]) = rs := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  simp

/-- The abstract rowMonodromy is the return map of the actual labeled
successor after traversing the literal old row list once. -/
theorem rowPortSuccessor_list_full_lap (rs : List (Row α)) (hR : 0 < rs.length)
    (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (p : Fin (h + 1)) :
    ((rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]) :
      Fin rs.length × Fin (h + 1) → Fin rs.length × Fin (h + 1))^[rs.length])
      (⟨0, hR⟩, p) = (⟨0, hR⟩, rowMonodromy h rs p) := by
  have hfull := rowPortSuccessor_full_lap hR h hn (fun i : Fin rs.length => rs[i.val])
    (fun i => hbase _ (List.getElem_mem i.isLt))
    (fun i => hkind _ (List.getElem_mem i.isLt)) p
  have hsum := congrArg (fun xs => (xs.map delta).sum) (finRange_map_list_getElem rs)
  simp only [List.map_map, Function.comp_def] at hsum
  rw [hsum] at hfull
  simpa only [rowMonodromy, walkPorts_eq_shift] using hfull

theorem rowPortSuccessor_list_full_lap_negative_excess (rs : List (Row α))
    (hR : 0 < rs.length) (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (p : Fin (h + 1)) :
    ((rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]) :
      Fin rs.length × Fin (h + 1) → Fin rs.length × Fin (h + 1))^[rs.length])
      (⟨0, hR⟩, p) =
        (⟨0, hR⟩, shiftPort h (-((rs.length : Int) - ((rs.map Row.charge).sum : Int))) p) := by
  rw [rowPortSuccessor_list_full_lap rs hR h hn hbase hkind,
    rowMonodromy_eq_negative_excess]

/-- First-coordinate iteration for any labeled successor with the cyclic row
projection. Port values may coincide freely. -/
theorem cyclicFirst_iterate_val {β : Type} (R : Nat) (hR : 0 < R)
    (S : Fin R × β → Fin R × β)
    (hfirst : ∀ ip, (S ip).1 = rowIndexPerm R hR ip.1)
    (ip : Fin R × β) (k : Nat) :
    ((S^[k] ip).1).val = (ip.1.val + k) % R := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt ip.1.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', hfirst, rowIndexPerm_val, ih, Nat.mod_add_mod]
    simp only [Nat.add_assoc]

/-- Repeating a literal whole-row lap repeats its return map on ports. -/
theorem cyclicFirst_iterate_laps {β : Type} (R : Nat) (hR : 0 < R)
    (S : Fin R × β → Fin R × β) (T : β → β)
    (hlap : ∀ p, S^[R] (⟨0, hR⟩, p) = (⟨0, hR⟩, T p)) (p : β) (k : Nat) :
    S^[R * k] (⟨0, hR⟩, p) = (⟨0, hR⟩, T^[k] p) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, hlap, ih,
      Function.iterate_succ_apply]

/-- A return to row zero must consist of an integral number of whole laps. -/
theorem cyclicFirst_return_dvd {β : Type} (R : Nat) (hR : 0 < R)
    (S : Fin R × β → Fin R × β)
    (hfirst : ∀ ip, (S ip).1 = rowIndexPerm R hR ip.1)
    (p : β) (k : Nat) (hreturn : S^[k] (⟨0, hR⟩, p) = (⟨0, hR⟩, p)) : R ∣ k := by
  have hval := cyclicFirst_iterate_val R hR S hfirst (⟨0, hR⟩, p) k
  rw [hreturn] at hval
  exact Nat.dvd_of_mod_eq_zero (by simpa using hval.symm)

end SuperpermutationUpperBound.Transport
