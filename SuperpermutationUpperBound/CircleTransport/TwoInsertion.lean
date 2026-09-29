import SuperpermutationUpperBound.Transport.OrbitCounts

/-! The tagged pair-port map for successive insertion of two new letters. -/
namespace SuperpermutationUpperBound.CircleTransport

open Transport

/-- Cyclic decrement on the first insertion port. -/
def decrement (h : Nat) (hh : 0 < h) : Equiv.Perm (Fin h) := (rowIndexPerm h hh).symm

theorem decrement_val (h : Nat) (hh : 0 < h) (p : Fin h) :
    (decrement h hh p).val = if p.val = 0 then h - 1 else p.val - 1 := by
  have he := rowIndexPerm_val h hh (decrement h hh p)
  have hs : rowIndexPerm h hh (decrement h hh p) = p :=
    (rowIndexPerm h hh).apply_symm_apply p
  rw [hs] at he
  have hp := (decrement h hh p).isLt
  by_cases hb : (decrement h hh p).val + 1 = h
  · rw [hb, Nat.mod_self] at he
    simp only [he, if_true]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at he
    have hpzero : p.val ≠ 0 := by omega
    simp only [if_neg hpzero]
    omega

/-- Full-row pair-port motion, written in literal modular coordinates. -/
def twoInsertion (h : Nat) (hh : 0 < h) : Equiv.Perm (Fin h × Fin (h + 1)) :=
  skewPerm (decrement h hh) (fun p => shiftPortPerm h (if p.val = 0 then -2 else -1))

@[simp] theorem twoInsertion_fst (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    (twoInsertion h hh pq).1 = decrement h hh pq.1 := rfl

@[simp] theorem twoInsertion_snd (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    (twoInsertion h hh pq).2 = shiftPort h (if pq.1.val = 0 then -2 else -1) pq.2 := rfl

/-- Subtracting the first port from the second exposes an invariant coordinate. -/
def pairChart (h : Nat) : Equiv.Perm (Fin h × Fin (h + 1)) where
  toFun pq := (pq.1, shiftPort h (-(pq.1.val : Int)) pq.2)
  invFun pr := (pr.1, shiftPort h (pr.1.val : Int) pr.2)
  left_inv pq := by simp [shiftPort_add]
  right_inv pr := by simp [shiftPort_add]

@[simp] theorem pairChart_fst (h : Nat) (pq : Fin h × Fin (h + 1)) :
    (pairChart h pq).1 = pq.1 := rfl

@[simp] theorem pairChart_snd (h : Nat) (pq : Fin h × Fin (h + 1)) :
    (pairChart h pq).2 = shiftPort h (-(pq.1.val : Int)) pq.2 := rfl

/-- In chart coordinates the map decrements only the first coordinate. -/
theorem pairChart_twoInsertion (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    pairChart h (twoInsertion h hh pq) =
      (decrement h hh pq.1, (pairChart h pq).2) := by
  apply Prod.ext
  · rfl
  · simp only [pairChart_snd, twoInsertion_fst, twoInsertion_snd, shiftPort_add, decrement_val]
    by_cases hp : pq.1.val = 0
    · simp only [hp, if_true, Int.natCast_zero, neg_zero, shiftPort_zero]
      have he : (-2 : Int) + -((h - 1 : Nat) : Int) = -((h + 1 : Nat) : Int) := by omega
      rw [he]
      exact (shiftPort_eq_self_iff h _ pq.2).mpr (dvd_neg.mpr (dvd_refl _))
    · simp only [if_neg hp]
      congr 1
      omega

/-- Iterated inverse motion has exactly the same returns as forward motion. -/
theorem inverse_period_iff {β : Type} (σ : Equiv.Perm β) (p : β) (k : Nat) :
    Function.IsPeriodicPt (σ.symm : β → β) k p ↔ Function.IsPeriodicPt (σ : β → β) k p := by
  have hl : Function.LeftInverse (σ : β → β) σ.symm := σ.apply_symm_apply
  have hr : Function.LeftInverse (σ.symm : β → β) σ := σ.symm_apply_apply
  constructor
  · intro hp
    have he := hl.iterate k p
    change (σ : β → β)^[k] p = p
    rw [show (σ.symm : β → β)^[k] p = p from hp] at he
    exact he
  · intro hp
    have he := hr.iterate k p
    change (σ.symm : β → β)^[k] p = p
    rw [show (σ : β → β)^[k] p = p from hp] at he
    exact he

theorem rowIndex_period_iff (h : Nat) (hh : 0 < h) (p : Fin h) (k : Nat) :
    Function.IsPeriodicPt (rowIndexPerm h hh : Fin h → Fin h) k p ↔ h ∣ k := by
  change (rowIndexPerm h hh : Fin h → Fin h)^[k] p = p ↔ _
  rw [Fin.ext_iff, rowIndexPerm_iterate_val]
  constructor
  · intro he
    have hm : p.val + k ≡ p.val + 0 [MOD h] := by
      simpa only [Nat.ModEq, Nat.add_zero, Nat.mod_eq_of_lt p.isLt] using he
    exact Nat.dvd_of_mod_eq_zero (Nat.ModEq.add_left_cancel (Nat.ModEq.refl p.val) hm)
  · intro hk
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hk, Nat.add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt p.isLt]

theorem decrement_period_iff (h : Nat) (hh : 0 < h) (p : Fin h) (k : Nat) :
    Function.IsPeriodicPt (decrement h hh : Fin h → Fin h) k p ↔ h ∣ k := by
  rw [decrement, inverse_period_iff, rowIndex_period_iff]

theorem pairChart_twoInsertion_iterate (h : Nat) (hh : 0 < h)
    (pq : Fin h × Fin (h + 1)) (k : Nat) :
    pairChart h ((twoInsertion h hh : _ → _)^[k] pq) =
      ((decrement h hh : Fin h → Fin h)^[k] pq.1, (pairChart h pq).2) := by
  induction k generalizing pq with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, twoInsertion_fst]
    have hs := congrArg Prod.snd (pairChart_twoInsertion h hh pq)
    rw [hs, Function.iterate_succ_apply]

theorem twoInsertion_period_iff (h : Nat) (hh : 0 < h)
    (pq : Fin h × Fin (h + 1)) (k : Nat) :
    Function.IsPeriodicPt (twoInsertion h hh : _ → _) k pq ↔ h ∣ k := by
  change (twoInsertion h hh : _ → _)^[k] pq = pq ↔ _
  rw [← (pairChart h).injective.eq_iff, pairChart_twoInsertion_iterate]
  have he : pairChart h pq = (pq.1, (pairChart h pq).2) := rfl
  rw [he, Prod.mk.injEq]
  simp only [and_true]
  exact decrement_period_iff h hh pq.1 k

/-- Exactly h full-row steps restore every tagged pair port. -/
theorem twoInsertion_full_period (h : Nat) (hh : 0 < h) :
    (twoInsertion h hh : _ → _)^[h] = id := by
  funext pq
  exact (twoInsertion_period_iff h hh pq h).mpr (dvd_refl _)

theorem twoInsertion_minimalPeriod (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    Function.minimalPeriod (twoInsertion h hh) pq = h := by
  apply Nat.dvd_antisymm
  · exact ((twoInsertion_period_iff h hh pq h).mpr (dvd_refl _)).minimalPeriod_dvd
  · exact (twoInsertion_period_iff h hh pq _).mp (Function.isPeriodicPt_minimalPeriod _ _)

/-- There are exactly h+1 pair-port orbits, each of length h, with every
pair-port occurrence retained once. -/
theorem twoInsertion_counted_orbit_partition (h : Nat) (hh : 0 < h) :
    ∃ orbits : List ((Fin h × Fin (h + 1)) × Nat),
      (∀ orbit ∈ orbits, orbit.2 = h ∧ 0 < orbit.2 ∧
        advance (twoInsertion h hh) orbit.1 orbit.2 = orbit.1) ∧
      (orbits.flatMap (fun orbit => orbitLabels (twoInsertion h hh) orbit.1 orbit.2)).Perm
        ((List.finRange h).product (List.finRange (h + 1))) ∧
      orbits.length = h + 1 := by
  obtain ⟨orbits, hreturns, hpartition, hcount⟩ :=
    finite_uniform_orbit_partition (twoInsertion h hh) h (twoInsertion_minimalPeriod h hh)
  refine ⟨orbits, hreturns, hpartition.trans ?_, ?_⟩
  · apply (List.perm_ext_iff_of_nodup Finset.univ.nodup_toList
      ((nodup_finRange h).product (nodup_finRange (h + 1)))).mpr
    intro pq
    simp only [Finset.mem_toList, Finset.mem_univ, true_iff]
    exact List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩
  · apply Nat.mul_right_cancel hh
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm h (h + 1)] using hcount

theorem rowIndex_zero_iff (h : Nat) (hh : 0 < h) (p : Fin h) :
    (rowIndexPerm h hh p).val = 0 ↔ p.val = h - 1 := by
  rw [rowIndexPerm_val]
  by_cases he : p.val + 1 = h
  · rw [he, Nat.mod_self]
    simp only [true_iff]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

@[simp] theorem twoInsertion_symm_fst (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    ((twoInsertion h hh).symm pq).1 = rowIndexPerm h hh pq.1 := rfl

/-- The inverse map increments the second port twice exactly at the last
first-coordinate port. -/
theorem twoInsertion_symm_snd (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    ((twoInsertion h hh).symm pq).2 =
      shiftPort h (if pq.1.val = h - 1 then 2 else 1) pq.2 := by
  change shiftPort h (-(if (rowIndexPerm h hh pq.1).val = 0 then -2 else -1)) pq.2 = _
  by_cases hp : pq.1.val = h - 1
  · have hz := (rowIndex_zero_iff h hh pq.1).mpr hp
    simp [hz, hp]
  · have hz : (rowIndexPerm h hh pq.1).val ≠ 0 :=
      fun hz => hp ((rowIndex_zero_iff h hh pq.1).mp hz)
    simp [hz, hp]

/-- Position of the completion letter after deleting the newly transported
letter from a tagged pair port. -/
def deleteLabel {h : Nat} (pq : Fin h × Fin (h + 1)) : Fin h :=
  ⟨pq.2.val - (if pq.1.val < pq.2.val then 1 else 0), by
    split <;> omega⟩

@[simp] theorem deleteLabel_val {h : Nat} (pq : Fin h × Fin (h + 1)) :
    (deleteLabel pq).val = pq.2.val - (if pq.1.val < pq.2.val then 1 else 0) := rfl

theorem shiftPort_neg_one_val_cases (h : Nat) (q : Fin (h + 1)) :
    (shiftPort h (-1) q).val = if q.val = 0 then h else q.val - 1 := by
  rw [shiftPort_negative_one_val]
  by_cases hq : q.val = 0
  · simp [hq]
  · have he : q.val + h = (q.val - 1) + (h + 1) := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [if_neg hq]

theorem shiftPort_neg_two_val_cases (h : Nat) (hh : 0 < h) (q : Fin (h + 1)) :
    (shiftPort h (-2) q).val =
      if q.val = 0 then h - 1 else if q.val = 1 then h else q.val - 2 := by
  have he : shiftPort h (-2) q = shiftPort h (-1) (shiftPort h (-1) q) := by
    rw [shiftPort_add]
    rfl
  rw [he, shiftPort_neg_one_val_cases, shiftPort_neg_one_val_cases]
  by_cases hq0 : q.val = 0
  · simp [hq0, Nat.ne_of_gt hh]
  · by_cases hq1 : q.val = 1
    · simp [hq1]
    · have hqpos : q.val - 1 ≠ 0 := by omega
      simp [hq0, hq1, hqpos, Nat.sub_sub]

/-- Deleting the new ordinary letter intertwines pair-port motion with the
old completion port's cyclic decrement. -/
theorem deleteLabel_twoInsertion (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    deleteLabel (twoInsertion h hh pq) = decrement h hh (deleteLabel pq) := by
  apply Fin.ext
  simp only [deleteLabel_val, twoInsertion_fst, twoInsertion_snd, decrement_val]
  by_cases hp : pq.1.val = 0
  · simp only [hp, if_true, shiftPort_neg_two_val_cases h hh]
    by_cases hq0 : pq.2.val = 0
    · simp [hq0]
    · by_cases hq1 : pq.2.val = 1
      · simp [hq1, Nat.sub_one_lt_of_lt (by omega : 0 < h)]
      · have hq2 : 2 ≤ pq.2.val := by omega
        have hlt : pq.2.val - 2 ≤ h - 1 := by omega
        simp [hq0, hq1, show ¬h - 1 < pq.2.val - 2 by omega,
          show 0 < pq.2.val by omega, show pq.2.val - 1 ≠ 0 by omega, Nat.sub_sub]
  · simp only [if_neg hp, shiftPort_neg_one_val_cases]
    by_cases hq0 : pq.2.val = 0
    · simp [hq0, show pq.1.val - 1 < h by omega]
    · simp only [if_neg hq0]
      by_cases hpq : pq.1.val < pq.2.val
      · have hpq' : pq.1.val - 1 < pq.2.val - 1 := by omega
        have hqpos : pq.2.val - 1 ≠ 0 := by omega
        simp [hpq, hpq', hqpos, Nat.sub_sub]
      · have hpq' : ¬pq.1.val - 1 < pq.2.val - 1 := by omega
        simp [hpq, hpq', hq0]

/-- Deletion intertwines every iterate, not just a single local step. -/
theorem deleteLabel_twoInsertion_iterate (h : Nat) (hh : 0 < h)
    (pq : Fin h × Fin (h + 1)) (k : Nat) :
    deleteLabel ((twoInsertion h hh : _ → _)^[k] pq) =
      (decrement h hh : Fin h → Fin h)^[k] (deleteLabel pq) := by
  have hs : Function.Semiconj (@deleteLabel h) (twoInsertion h hh) (decrement h hh) :=
    deleteLabel_twoInsertion h hh
  exact hs.iterate_right k pq

/-- Distinct pair ports with the same old deletion label belong to different
pair-port orbits. Tagged equal boundary tuples therefore cause no ambiguity. -/
theorem sameCycle_same_deleteLabel_eq (h : Nat) (hh : 0 < h)
    (pq pr : Fin h × Fin (h + 1)) (hsame : (twoInsertion h hh).SameCycle pq pr)
    (hdelete : deleteLabel pq = deleteLabel pr) : pq = pr := by
  obtain ⟨k, hk⟩ := hsame.exists_nat_pow_eq
  have he : (twoInsertion h hh : _ → _)^[k] pq = pr := by
    simpa only [Equiv.Perm.iterate_eq_pow] using hk
  have hd : Function.IsPeriodicPt (decrement h hh : Fin h → Fin h) k (deleteLabel pq) := by
    change (decrement h hh : Fin h → Fin h)^[k] (deleteLabel pq) = deleteLabel pq
    rw [← deleteLabel_twoInsertion_iterate, he, hdelete]
  have hpair := (twoInsertion_period_iff h hh pq k).mpr ((decrement_period_iff h hh _ k).mp hd)
  exact (show (twoInsertion h hh : _ → _)^[k] pq = pq from hpair).symm.trans he

theorem decrement_val_mod (h : Nat) (hh : 0 < h) (p : Fin h) :
    ((decrement h hh p).val : Int) = ((p.val : Int) - 1) % (h : Int) := by
  rw [decrement_val]
  by_cases hp : p.val = 0
  · simp only [if_pos hp]
    have he : (p.val : Int) - 1 + (h : Int) = ((h - 1 : Nat) : Int) := by omega
    rw [← Int.add_emod_right ((p.val : Int) - 1) (h : Int), he,
      Int.emod_eq_of_lt (by omega) (by omega)]
  · simp only [if_neg hp]
    rw [Int.natCast_sub (by omega : 1 ≤ p.val)]
    exact (Int.emod_eq_of_lt (by omega) (by omega)).symm

/-- Literal modular coordinates of the full-row two-insertion map. -/
theorem twoInsertion_modular (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    ((twoInsertion h hh pq).1.val : Int) = ((pq.1.val : Int) - 1) % (h : Int) ∧
    ((twoInsertion h hh pq).2.val : Int) =
      ((pq.2.val : Int) - 1 - (if pq.1.val = 0 then 1 else 0)) % ((h + 1 : Nat) : Int) := by
  constructor
  · exact decrement_val_mod h hh pq.1
  · rw [twoInsertion_snd, shiftPort_val]
    congr 1
    split <;> omega

/-- Literal modular coordinates of the inverse, used for old short rows. -/
theorem twoInsertion_symm_modular (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    ((twoInsertion h hh).symm pq).1.val = (pq.1.val + 1) % h ∧
    (((twoInsertion h hh).symm pq).2.val : Int) =
      ((pq.2.val : Int) + 1 + (if pq.1.val = h - 1 then 1 else 0)) % ((h + 1 : Nat) : Int) := by
  constructor
  · exact rowIndexPerm_val h hh pq.1
  · rw [twoInsertion_symm_snd, shiftPort_val]
    congr 1
    split <;> omega

theorem deleteLabel_twoInsertion_modular (h : Nat) (hh : 0 < h) (pq : Fin h × Fin (h + 1)) :
    ((deleteLabel (twoInsertion h hh pq)).val : Int) =
      (((deleteLabel pq).val : Int) - 1) % (h : Int) := by
  rw [deleteLabel_twoInsertion, decrement_val_mod]

/-- Every T-orbit meets each old completion label. Combined with
sameCycle_same_deleteLabel_eq, the meeting is unique within that orbit. -/
theorem twoInsertion_orbit_meets_deleteLabel (h : Nat) (hh : 0 < h)
    (pq : Fin h × Fin (h + 1)) (j : Fin h) :
    ∃ k < h, deleteLabel ((twoInsertion h hh : _ → _)^[k] pq) = j := by
  have hm : Function.minimalPeriod (decrement h hh) (deleteLabel pq) = h := by
    apply Nat.dvd_antisymm
    · exact ((decrement_period_iff h hh _ h).mpr (dvd_refl _)).minimalPeriod_dvd
    · exact (decrement_period_iff h hh _ _).mp (Function.isPeriodicPt_minimalPeriod _ _)
  have hn : (orbitLabels (decrement h hh) (deleteLabel pq) h).Nodup := by
    simpa only [hm] using orbitLabels_minimalPeriod_nodup (decrement h hh) (deleteLabel pq)
  have hp : (orbitLabels (decrement h hh) (deleteLabel pq) h).Perm (List.finRange h) :=
    perm_of_nodup_subset_length hn (fun a _ => List.mem_finRange a) (by simp)
  have hj := hp.mem_iff.mpr (List.mem_finRange j)
  rw [orbitLabels_eq_map_iterate] at hj
  obtain ⟨k, hk, hkj⟩ := List.mem_map.mp hj
  exact ⟨k, List.mem_range.mp hk, (deleteLabel_twoInsertion_iterate h hh pq k).trans hkj⟩

end SuperpermutationUpperBound.CircleTransport
