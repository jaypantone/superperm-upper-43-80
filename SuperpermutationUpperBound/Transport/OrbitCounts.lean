import SuperpermutationUpperBound.Transport.FullLap

/-! Arithmetic of finite cyclic port orbits, keeping the signed displacement
separate from the occurrence labels used for row assembly. -/
namespace SuperpermutationUpperBound.Transport

variable {α β : Type}

theorem shiftPort_iterate (h : Nat) (d : Int) (p : Fin (h + 1)) (k : Nat) :
    (shiftPort h d)^[k] p = shiftPort h ((k : Int) * d) p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, shiftPort_add]
    congr 1
    simp [Int.add_mul]

theorem shiftPort_eq_self_iff (h : Nat) (d : Int) (p : Fin (h + 1)) :
    shiftPort h d p = p ↔ ((h + 1 : Nat) : Int) ∣ d := by
  have hp : ((p.val : Int) % ((h + 1 : Nat) : Int)) = p.val :=
    Int.emod_eq_of_lt (by omega) (by omega)
  constructor
  · intro heq
    have hv := congrArg (fun q : Fin (h + 1) => (q.val : Int)) heq
    rw [shiftPort_val] at hv
    have hv : ((p.val : Int) + d) % ((h + 1 : Nat) : Int) =
        (p.val : Int) % ((h + 1 : Nat) : Int) := hv.trans hp.symm
    have hd := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hv
    simpa only [add_sub_cancel_left] using (Int.dvd_iff_emod_eq_zero.mpr hd)
  · intro hd
    apply Fin.ext
    apply Int.ofNat_inj.mp
    rw [shiftPort_val, Int.add_emod, Int.emod_eq_zero_of_dvd hd, Int.add_zero,
      Int.emod_emod, hp]

theorem shiftPort_period_iff (h : Nat) (d : Int) (p : Fin (h + 1)) (k : Nat) :
    Function.IsPeriodicPt (shiftPort h d) k p ↔
      ((h + 1 : Nat) : Int) ∣ (k : Int) * d := by
  change (shiftPort h d)^[k] p = p ↔ _
  rw [shiftPort_iterate, shiftPort_eq_self_iff]

theorem shiftPort_negative_one_period_iff (h : Nat) (p : Fin (h + 1)) (k : Nat) :
    Function.IsPeriodicPt (shiftPort h (-1)) k p ↔ h + 1 ∣ k := by
  rw [shiftPort_period_iff, Int.mul_neg_one, Int.dvd_neg]
  exact Int.natCast_dvd_natCast

theorem shiftPort_negative_one_minimalPeriod (h : Nat) (p : Fin (h + 1)) :
    Function.minimalPeriod (shiftPort h (-1)) p = h + 1 := by
  apply Nat.dvd_antisymm
  · exact (shiftPort_negative_one_period_iff h p (h + 1)).mpr (dvd_refl _)
      |>.minimalPeriod_dvd
  · exact (shiftPort_negative_one_period_iff h p _).mp
      (Function.isPeriodicPt_minimalPeriod _ _)

/-- The negative translation by a natural excess has period modulus/gcd,
including zero excess and singleton port spaces. -/
theorem shiftPort_negative_minimalPeriod (h w : Nat) (p : Fin (h + 1)) :
    Function.minimalPeriod (shiftPort h (-(w : Int))) p = (h + 1) / Nat.gcd (h + 1) w := by
  have hfunc : shiftPort h (-(w : Int)) = (shiftPort h (-1))^[w] := by
    funext p
    rw [shiftPort_iterate]
    simp
  rw [hfunc, Function.minimalPeriod_iterate_eq_div_gcd'
    (Function.mk_mem_periodicPts (Nat.succ_pos h)
      ((shiftPort_negative_one_period_iff h p (h + 1)).mpr (dvd_refl _))),
    shiftPort_negative_one_minimalPeriod]

/-- Changing the orientation does not change a translation's cycle length. -/
theorem shiftPort_minimalPeriod_neg (h : Nat) (d : Int) (p : Fin (h + 1)) :
    Function.minimalPeriod (shiftPort h (-d)) p =
      Function.minimalPeriod (shiftPort h d) p := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro k
  rw [shiftPort_period_iff, shiftPort_period_iff]
  simp only [Int.mul_neg, Int.dvd_neg]

theorem shiftPort_minimalPeriod (h : Nat) (d : Int) (p : Fin (h + 1)) :
    Function.minimalPeriod (shiftPort h d) p = (h + 1) / Nat.gcd (h + 1) d.natAbs := by
  cases d with
  | ofNat w =>
    rw [← shiftPort_minimalPeriod_neg]
    exact shiftPort_negative_minimalPeriod h w p
  | negSucc w =>
    exact shiftPort_negative_minimalPeriod h (w + 1) p

/-- Any nonempty returning orbit with no repeated labels already has minimal
period. This lets an occurrence partition expose exact cycle lengths. -/
theorem orbitLabels_nodup_returning_period (next : β → β) (start : β) (k : Nat)
    (hk : 0 < k) (hreturn : advance next start k = start)
    (hnodup : (orbitLabels next start k).Nodup) :
    k = Function.minimalPeriod next start := by
  have hperiod : Function.IsPeriodicPt next k start := by
    simpa only [advance_eq_iterate, Function.IsPeriodicPt, Function.IsFixedPt] using hreturn
  have hmpos := hperiod.minimalPeriod_pos hk
  have hmle := hperiod.minimalPeriod_le hk
  apply Nat.le_antisymm _ hmle
  by_contra hnle
  have hmlt : Function.minimalPeriod next start < k := by omega
  rw [orbitLabels_eq_map_iterate] at hnodup
  have hinj := (List.nodup_map_iff_inj_on List.nodup_range).mp hnodup
  have heq : 0 = Function.minimalPeriod next start :=
    hinj 0 (List.mem_range.mpr hk) _ (List.mem_range.mpr hmlt)
      (by simp only [Function.iterate_zero_apply, Function.iterate_minimalPeriod])
  omega

/-- An exact finite occurrence partition into uniform minimal orbits has the
expected number of components; no distinctness of path endpoints is used. -/
theorem finite_uniform_orbit_partition [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm β) (L : Nat) (hperiod : ∀ b, Function.minimalPeriod σ b = L) :
    ∃ orbits : List (β × Nat),
      (∀ orbit ∈ orbits, orbit.2 = L ∧ 0 < orbit.2 ∧
        advance σ orbit.1 orbit.2 = orbit.1) ∧
      (orbits.flatMap (fun orbit => orbitLabels σ orbit.1 orbit.2)).Perm
        (Finset.univ : Finset β).toList ∧
      orbits.length * L = Fintype.card β := by
  obtain ⟨orbits, hreturns, hpartition⟩ :=
    invariant_finset_orbit_partition σ Finset.univ (by simp)
  have hnodup := hpartition.nodup_iff.mpr Finset.univ.nodup_toList
  have hlengths : ∀ orbit ∈ orbits, orbit.2 = L := by
    intro orbit horbit
    rw [orbitLabels_nodup_returning_period σ orbit.1 orbit.2
      (hreturns orbit horbit).1 (hreturns orbit horbit).2
      ((List.nodup_flatMap.mp hnodup).1 orbit horbit), hperiod]
  refine ⟨orbits, fun orbit horbit => ⟨hlengths orbit horbit, hreturns orbit horbit⟩,
    hpartition, ?_⟩
  have hmap : orbits.map (fun orbit => orbit.2) = orbits.map (fun _ => L) :=
    List.map_congr_left hlengths
  have hcount := hpartition.length_eq
  simp only [List.length_flatMap, orbitLabels_length] at hcount
  rw [hmap] at hcount
  simpa using hcount

/-- The signed port translation as an explicitly invertible permutation. -/
def shiftPortPerm (h : Nat) (d : Int) : Equiv.Perm (Fin (h + 1)) where
  toFun := shiftPort h d
  invFun := shiftPort h (-d)
  left_inv := shiftPort_inverse h d
  right_inv := shiftPort_inverse_right h d

@[simp] theorem shiftPortPerm_apply (h : Nat) (d : Int) (p : Fin (h + 1)) :
    shiftPortPerm h d p = shiftPort h d p := rfl

/-- The translation has exactly gcd(modulus, absolute displacement) orbits,
with a literal occurrence partition and uniform positive orbit lengths. -/
theorem shiftPort_counted_orbit_partition (h : Nat) (d : Int) :
    ∃ orbits : List (Fin (h + 1) × Nat),
      (∀ orbit ∈ orbits, orbit.2 = (h + 1) / Nat.gcd (h + 1) d.natAbs ∧
        0 < orbit.2 ∧ advance (shiftPort h d) orbit.1 orbit.2 = orbit.1) ∧
      (orbits.flatMap (fun orbit => orbitLabels (shiftPort h d) orbit.1 orbit.2)).Perm
        (List.finRange (h + 1)) ∧
      orbits.length = Nat.gcd (h + 1) d.natAbs := by
  obtain ⟨orbits, hreturns, hpartition, hcount⟩ :=
    finite_uniform_orbit_partition (shiftPortPerm h d) _ (shiftPort_minimalPeriod h d)
  refine ⟨orbits, hreturns, hpartition.trans ?_, ?_⟩
  · apply (List.perm_ext_iff_of_nodup Finset.univ.nodup_toList
      (nodup_finRange (h + 1))).mpr
    intro a
    simp [List.mem_finRange]
  · have hdiv := Nat.mul_div_cancel' (Nat.gcd_dvd_left (h + 1) d.natAbs)
    have hpos : 0 < (h + 1) / Nat.gcd (h + 1) d.natAbs := by
      rw [← shiftPort_minimalPeriod h d ⟨0, by omega⟩]
      exact Function.minimalPeriod_pos_of_mem_periodicPts
        ((shiftPortPerm h d).injective.mem_periodicPts _)
    apply Nat.mul_right_cancel hpos
    have hc : orbits.length * ((h + 1) / Nat.gcd (h + 1) d.natAbs) = h + 1 := by
      simpa only [Fintype.card_fin] using hcount
    exact hc.trans hdiv.symm

/-- The minimal return of a row-zero state is one port period's worth of
complete row laps. -/
theorem cyclicFirst_minimalPeriod_zero (R : Nat) (hR : 0 < R)
    (S : Fin R × β → Fin R × β) (T : β → β)
    (hfirst : ∀ ip, (S ip).1 = rowIndexPerm R hR ip.1)
    (hlap : ∀ p, S^[R] (⟨0, hR⟩, p) = (⟨0, hR⟩, T p)) (p : β) :
    Function.minimalPeriod S (⟨0, hR⟩, p) = R * Function.minimalPeriod T p := by
  apply Nat.dvd_antisymm
  · have hp : Function.IsPeriodicPt S (R * Function.minimalPeriod T p) (⟨0, hR⟩, p) := by
      change S^[R * Function.minimalPeriod T p] (⟨0, hR⟩, p) = (⟨0, hR⟩, p)
      rw [cyclicFirst_iterate_laps R hR S T hlap, Function.iterate_minimalPeriod]
    exact hp.minimalPeriod_dvd
  · have hret := Function.iterate_minimalPeriod (f := S) (x := (⟨0, hR⟩, p))
    obtain ⟨k, hk⟩ := cyclicFirst_return_dvd R hR S hfirst p _ hret
    have hp : Function.IsPeriodicPt T k p := by
      change T^[k] p = p
      rw [hk, cyclicFirst_iterate_laps R hR S T hlap] at hret
      exact congrArg Prod.snd hret
    rw [hk]
    exact Nat.mul_dvd_mul_left R hp.minimalPeriod_dvd

/-- If the return map has uniform period, so does the actual successor on
all row/port labels, regardless of the starting row. -/
theorem cyclicFirst_minimalPeriod [Finite β] (R : Nat) (hR : 0 < R)
    (S : Equiv.Perm (Fin R × β)) (T : β → β)
    (hfirst : ∀ ip, (S ip).1 = rowIndexPerm R hR ip.1)
    (hlap : ∀ p, (S : Fin R × β → Fin R × β)^[R] (⟨0, hR⟩, p) = (⟨0, hR⟩, T p))
    (L : Nat) (hperiod : ∀ p, Function.minimalPeriod T p = L) (ip : Fin R × β) :
    Function.minimalPeriod S ip = R * L := by
  let k := R - ip.1.val
  let jp := (S : Fin R × β → Fin R × β)^[k] ip
  have hzero : jp.1 = ⟨0, hR⟩ := by
    apply Fin.ext
    change ((S : Fin R × β → Fin R × β)^[k] ip).1.val = 0
    rw [cyclicFirst_iterate_val R hR S hfirst]
    simp [k, Nat.add_sub_of_le ip.1.isLt.le]
  have heq : jp = (⟨0, hR⟩, jp.2) := Prod.ext hzero rfl
  have hm := Function.minimalPeriod_apply_iterate (S.injective.mem_periodicPts ip) k
  change Function.minimalPeriod S jp = Function.minimalPeriod S ip at hm
  rw [← hm, heq, cyclicFirst_minimalPeriod_zero R hR S T hfirst hlap, hperiod]

/-- Exact period of every actual row/port label in terms of the signed old
row excess. Here the old ordinary size is h+2 and the port count is h+1. -/
theorem rowPortSuccessor_list_minimalPeriod (rs : List (Row α)) (hR : 0 < rs.length)
    (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (ip : Fin rs.length × Fin (h + 1)) :
    Function.minimalPeriod
      (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val])) ip =
      rs.length * ((h + 1) / Nat.gcd (h + 1)
        (((rs.length : Int) - ((rs.map Row.charge).sum : Int)).natAbs)) := by
  apply cyclicFirst_minimalPeriod rs.length hR _
    (shiftPort h (-((rs.length : Int) - ((rs.map Row.charge).sum : Int))))
    (fun ip => rowPortSuccessor_fst hR (h + 2) hn _ ip)
    (rowPortSuccessor_list_full_lap_negative_excess rs hR h hn hbase hkind)
  intro p
  simpa only [Int.natAbs_neg] using
    shiftPort_minimalPeriod h (-((rs.length : Int) - ((rs.map Row.charge).sum : Int))) p

/-- The actual labeled row/port successor has exactly gcd(port count, signed
excess) minimal orbits. The inventory is the full literal product of row
occurrences and input ports. -/
theorem rowPortSuccessor_list_counted_orbit_partition (rs : List (Row α))
    (hR : 0 < rs.length) (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ∃ orbits : List ((Fin rs.length × Fin (h + 1)) × Nat),
      (∀ orbit ∈ orbits,
        orbit.2 = rs.length * ((h + 1) / Nat.gcd (h + 1)
          (((rs.length : Int) - ((rs.map Row.charge).sum : Int)).natAbs)) ∧
        0 < orbit.2 ∧ advance
          (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]))
          orbit.1 orbit.2 = orbit.1) ∧
      (orbits.flatMap (fun orbit => orbitLabels
        (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]))
        orbit.1 orbit.2)).Perm
          ((List.finRange rs.length).product (List.finRange (h + 1))) ∧
      orbits.length = Nat.gcd (h + 1)
        (((rs.length : Int) - ((rs.map Row.charge).sum : Int)).natAbs) := by
  obtain ⟨orbits, hreturns, hpartition, hcount⟩ :=
    finite_uniform_orbit_partition
      (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val])) _
      (rowPortSuccessor_list_minimalPeriod rs hR h hn hbase hkind)
  refine ⟨orbits, hreturns, hpartition.trans ?_, ?_⟩
  · apply (List.perm_ext_iff_of_nodup Finset.univ.nodup_toList
      ((nodup_finRange rs.length).product (nodup_finRange (h + 1)))).mpr
    intro a
    simp only [Finset.mem_toList, Finset.mem_univ, true_iff]
    exact List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩
  · let w := ((rs.length : Int) - ((rs.map Row.charge).sum : Int))
    let c := Nat.gcd (h + 1) w.natAbs
    let L := (h + 1) / c
    have hdiv : c * L = h + 1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hpos : 0 < L := by
      change 0 < (h + 1) / Nat.gcd (h + 1) w.natAbs
      rw [← shiftPort_minimalPeriod h w ⟨0, by omega⟩]
      exact Function.minimalPeriod_pos_of_mem_periodicPts
        ((shiftPortPerm h w).injective.mem_periodicPts _)
    change orbits.length = c
    apply Nat.mul_right_cancel hpos
    apply Nat.mul_right_cancel hR
    calc
      (orbits.length * L) * rs.length = orbits.length * (rs.length * L) := by ac_rfl
      _ = rs.length * (h + 1) := by
        have hsize : h + 2 - 1 = h + 1 := by omega
        simpa only [Fintype.card_prod, Fintype.card_fin, hsize] using hcount
      _ = (c * L) * rs.length := by rw [hdiv, Nat.mul_comm]

/-- The counted orbit partition assembles actual nonempty compatible paths
into exactly the prescribed number of closed literal row trails. -/
theorem rowPortSuccessor_counted_path_assembly (rs : List (Row α))
    (hR : 0 < rs.length) (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (paths : Fin rs.length × Fin (h + 1) → List (Row α))
    (hpaths : ∀ ip, paths ip ≠ [])
    (hinternal : ∀ ip, RowTrailCompatible ((paths ip).head (hpaths ip)) (paths ip).tail)
    (hboundary : ∀ ip, ((paths ip).getLast (hpaths ip)).Compatible
      ((paths (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]) ip)).head
        (hpaths _))) :
    ∃ trails : List (List (Row α)),
      (∀ trail ∈ trails, ClosedTrail trail) ∧
      trails.flatten.Perm
        (((List.finRange rs.length).product (List.finRange (h + 1))).flatMap paths) ∧
      trails.length = Nat.gcd (h + 1)
        (((rs.length : Int) - ((rs.map Row.charge).sum : Int)).natAbs) := by
  obtain ⟨orbits, hreturns, hpartition, hcount⟩ :=
    rowPortSuccessor_list_counted_orbit_partition rs hR h hn hbase hkind
  obtain ⟨trails, hclosed, hinventory, hlength⟩ := assembly_of_orbit_partition paths
    (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]))
    hpaths hinternal hboundary _ orbits (fun orbit horbit => (hreturns orbit horbit).2) hpartition
  exact ⟨trails, hclosed, hinventory, hlength.trans hcount⟩

end SuperpermutationUpperBound.Transport
