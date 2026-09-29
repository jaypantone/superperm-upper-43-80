import SuperpermutationUpperBound.Transport.OrbitAssembly
import SuperpermutationUpperBound.Foundation.Relabeling
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! A finite permutation partitions its labels into minimal positive returning
orbits, including one-element fixed-point orbits. The assembly bridge then
preserves every literal row occurrence. -/
namespace SuperpermutationUpperBound.Transport

variable {α β : Type}

theorem advance_eq_iterate (next : β → β) (start : β) (k : Nat) :
    advance next start k = next^[k] start := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih => rw [advance, ih, Function.iterate_succ_apply]

theorem orbitLabels_eq_map_iterate (next : β → β) (start : β) (k : Nat) :
    orbitLabels next start k = (List.range k).map (fun j => next^[j] start) := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
    rw [orbitLabels, List.range_succ_eq_map, List.map_cons, List.map_map, ih]
    simp only [Function.iterate_zero_apply, Function.comp_def, Function.iterate_succ_apply]

theorem orbitLabels_minimalPeriod_nodup (next : β → β) (start : β) :
    (orbitLabels next start (Function.minimalPeriod next start)).Nodup := by
  rw [orbitLabels_eq_map_iterate]
  apply (List.nodup_map_iff_inj_on (List.nodup_range)).mpr
  intro i hi j hj heq
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
    (List.mem_range.mp hi) (List.mem_range.mp hj)).mp heq

theorem mem_orbitLabels_minimalPeriod [Finite β] (σ : Equiv.Perm β) (start target : β) :
    target ∈ orbitLabels σ start (Function.minimalPeriod σ start) ↔ σ.SameCycle start target := by
  rw [orbitLabels_eq_map_iterate]
  constructor
  · intro ht
    obtain ⟨j, _, heq⟩ := List.mem_map.mp ht
    have hsc := (Equiv.Perm.SameCycle.refl σ start).pow_right (n := j)
    simpa only [← σ.iterate_eq_pow, heq] using hsc
  · intro ht
    obtain ⟨j, hj⟩ := ht.exists_nat_pow_eq
    refine List.mem_map.mpr ⟨j % Function.minimalPeriod σ start,
      List.mem_range.mpr (Nat.mod_lt _ (Function.minimalPeriod_pos_of_mem_periodicPts
        (σ.injective.mem_periodicPts start))), ?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq, σ.iterate_eq_pow]
    exact hj

theorem minimalOrbit_return [Finite β] (σ : Equiv.Perm β) (start : β) :
    0 < Function.minimalPeriod σ start ∧
      advance σ start (Function.minimalPeriod σ start) = start := by
  exact ⟨Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts start),
    (advance_eq_iterate σ start _).trans Function.iterate_minimalPeriod⟩

/-- Fixed points contribute a singleton orbit rather than disappearing. -/
theorem minimalOrbit_of_fixedPoint (σ : Equiv.Perm β) {start : β} (hfixed : σ start = start) :
    orbitLabels σ start (Function.minimalPeriod σ start) = [start] := by
  have hp : Function.minimalPeriod σ start = 1 :=
    Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfixed
  rw [hp]
  rfl

theorem mem_minimalOrbit_apply_iff [Finite β] (σ : Equiv.Perm β) (start target : β) :
    σ target ∈ orbitLabels σ start (Function.minimalPeriod σ start) ↔
      target ∈ orbitLabels σ start (Function.minimalPeriod σ start) := by
  rw [mem_orbitLabels_minimalPeriod, mem_orbitLabels_minimalPeriod,
    Equiv.Perm.sameCycle_apply_right]

theorem iterate_mem_closed_finset [DecidableEq β] (next : β → β) (S : Finset β)
    (hclosed : ∀ a ∈ S, next a ∈ S) {start : β} (hs : start ∈ S) (k : Nat) :
    next^[k] start ∈ S := by
  induction k generalizing start with
  | zero => exact hs
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (hclosed start hs)

theorem minimalOrbit_subset [Finite β] [DecidableEq β] (σ : Equiv.Perm β) (S : Finset β)
    (hclosed : ∀ a ∈ S, σ a ∈ S) {start : β} (hs : start ∈ S) :
    (orbitLabels σ start (Function.minimalPeriod σ start)).toFinset ⊆ S := by
  intro target ht
  rw [List.mem_toFinset, mem_orbitLabels_minimalPeriod] at ht
  obtain ⟨j, rfl⟩ := ht.exists_nat_pow_eq
  simpa only [σ.iterate_eq_pow] using iterate_mem_closed_finset σ S hclosed hs j

/-- Remove one minimal positive orbit at a time from a successor-invariant
finite set. Singleton fixed-point orbits are handled by the same proof. -/
theorem invariant_finset_orbit_partition [Finite β] [DecidableEq β]
    (σ : Equiv.Perm β) (S : Finset β) (hclosed : ∀ a ∈ S, σ a ∈ S) :
    ∃ orbits : List (β × Nat),
      (∀ orbit ∈ orbits, 0 < orbit.2 ∧ advance σ orbit.1 orbit.2 = orbit.1) ∧
      (orbits.flatMap (fun orbit => orbitLabels σ orbit.1 orbit.2)).Perm S.toList := by
  classical
  revert hclosed
  refine Finset.strongInductionOn S ?_
  intro S ih hclosed
  by_cases hS : S.Nonempty
  · obtain ⟨start, hs⟩ := hS
    let period := Function.minimalPeriod σ start
    let cycle := orbitLabels σ start period
    let remaining := S \ cycle.toFinset
    have hsub : cycle.toFinset ⊆ S := minimalOrbit_subset σ S hclosed hs
    have hstart : start ∈ cycle :=
      (mem_orbitLabels_minimalPeriod σ start start).mpr (Equiv.Perm.SameCycle.refl σ start)
    have hne : cycle.toFinset.Nonempty := ⟨start, List.mem_toFinset.mpr hstart⟩
    have hsmaller : remaining ⊂ S := Finset.sdiff_ssubset hsub hne
    have hremaining : ∀ a ∈ remaining, σ a ∈ remaining := by
      intro a ha
      obtain ⟨haS, haC⟩ := Finset.mem_sdiff.mp ha
      apply Finset.mem_sdiff.mpr
      refine ⟨hclosed a haS, ?_⟩
      intro hnext
      apply haC
      apply List.mem_toFinset.mpr
      exact (mem_minimalOrbit_apply_iff σ start a).mp (List.mem_toFinset.mp hnext)
    obtain ⟨orbits, hperiods, hperm⟩ := ih remaining hsmaller hremaining
    refine ⟨(start, period) :: orbits, ?_, ?_⟩
    · intro orbit horbit
      rcases List.mem_cons.mp horbit with rfl | horbit
      · exact minimalOrbit_return σ start
      · exact hperiods orbit horbit
    · change (cycle ++ orbits.flatMap (fun orbit => orbitLabels σ orbit.1 orbit.2)).Perm S.toList
      have hnodup : (cycle ++ orbits.flatMap (fun orbit => orbitLabels σ orbit.1 orbit.2)).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨orbitLabels_minimalPeriod_nodup σ start,
          hperm.nodup_iff.mpr remaining.nodup_toList, ?_⟩
        intro a ha b hb heq
        subst b
        have haR : a ∈ remaining := Finset.mem_toList.mp (hperm.mem_iff.mp hb)
        exact (Finset.mem_sdiff.mp haR).2 (List.mem_toFinset.mpr ha)
      apply (List.perm_ext_iff_of_nodup hnodup S.nodup_toList).mpr
      intro a
      rw [List.mem_append, hperm.mem_iff, Finset.mem_toList, Finset.mem_toList]
      constructor
      · intro ha
        rcases ha with ha | ha
        · exact hsub (List.mem_toFinset.mpr ha)
        · exact (Finset.mem_sdiff.mp ha).1
      · intro haS
        by_cases haC : a ∈ cycle
        · exact Or.inl haC
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨haS, by simpa using haC⟩)
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    exact ⟨[], by simp, by simp⟩

/-- Every finite permutation has a partition into positive returning label
orbits, with occurrence multiplicity exactly one for every label. -/
theorem finite_permutation_orbit_partition {N : Nat} (σ : Equiv.Perm (Fin N)) :
    ∃ orbits : List (Fin N × Nat),
      (∀ orbit ∈ orbits, 0 < orbit.2 ∧ advance σ orbit.1 orbit.2 = orbit.1) ∧
      (orbits.flatMap (fun orbit => orbitLabels σ orbit.1 orbit.2)).Perm (List.finRange N) := by
  obtain ⟨orbits, hperiods, hperm⟩ := invariant_finset_orbit_partition σ Finset.univ (by simp)
  refine ⟨orbits, hperiods, hperm.trans ?_⟩
  apply (List.perm_ext_iff_of_nodup Finset.univ.nodup_toList (nodup_finRange N)).mpr
  intro a
  simp [List.mem_finRange]

/-- A finite bijective successor assembles all labeled literal paths into
closed trails, preserving every row occurrence even when row values coincide. -/
theorem finite_permutation_path_assembly {N : Nat} (σ : Equiv.Perm (Fin N))
    (paths : Fin N → List (Row α)) (hpaths : ∀ i, paths i ≠ [])
    (hinternal : ∀ i, RowTrailCompatible ((paths i).head (hpaths i)) (paths i).tail)
    (hboundary : ∀ i, ((paths i).getLast (hpaths i)).Compatible
      ((paths (σ i)).head (hpaths (σ i)))) :
    ∃ trails : List (List (Row α)), (∀ trail ∈ trails, ClosedTrail trail) ∧
      trails.flatten.Perm ((List.finRange N).flatMap paths) := by
  obtain ⟨orbits, hperiods, hpartition⟩ := finite_permutation_orbit_partition σ
  obtain ⟨trails, hclosed, hperm, _⟩ := assembly_of_orbit_partition paths σ hpaths
    hinternal hboundary (List.finRange N) orbits hperiods hpartition
  exact ⟨trails, hclosed, hperm⟩

end SuperpermutationUpperBound.Transport
