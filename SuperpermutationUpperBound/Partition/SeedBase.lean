import SuperpermutationUpperBound.Partition.Basic
import SuperpermutationUpperBound.Certificates.SmallSeed
import Mathlib.Data.List.Permutation

/-!
Six-symbol block accounting from the six original closed seeds. The 24
additional full rows fill the missing cyclic blocks for counting purposes.
No claim is made that these added rows form closed trails at this size.
-/

namespace SuperpermutationUpperBound.Partition.SeedBase

def alphabet6 : List Nat := [0, 1, 2, 3, 4, 5]

/-- The original checked rows, relabeled by the literal values of `Fin 7`. -/
def seedRowsNat : List (Row Nat) :=
  Certificates.SmallSeed.allRows.map (fun r =>
    ⟨r.base.map Fin.val, 6, r.visible⟩)

def canonicalBases6 : List (List Nat) :=
  (List.permutations [1, 2, 3, 4, 5]).map (fun tail => 0 :: tail)

def unusedBases6 : List (List Nat) :=
  canonicalBases6.filter (fun x => decide (∀ r ∈ seedRowsNat, ¬ CyclicEq r.base x))

/-- A block accounting family, with no asserted trail structure for its tail. -/
def accountingRows6 : List (Row Nat) :=
  seedRowsNat ++ unusedBases6.map (fun x => ⟨x, 6, 6⟩)

theorem canonicalBases6_perm {x : List Nat} (hx : x ∈ canonicalBases6) :
    x.Perm alphabet6 := by
  obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hx
  exact (List.mem_permutations.mp ht).cons 0

theorem canonicalBases6_length {x : List Nat} (hx : x ∈ canonicalBases6) :
    x.length = 6 :=
  (canonicalBases6_perm hx).length_eq

/-- Every ordinary permutation rotates to exactly the form enumerated by the
canonical list: cut immediately before its unique zero.
-/
theorem canonicalBases6_complete {x : List Nat} (hx : x.Perm alphabet6) :
    ∃ b ∈ canonicalBases6, CyclicEq b x := by
  have hzero : 0 ∈ x := hx.mem_iff.mpr (by decide)
  obtain ⟨a, b, rfl, _⟩ := List.eq_append_cons_of_mem hzero
  have hn : a ++ 0 :: b ≠ [] := by simp
  have hc : CyclicEq (a ++ 0 :: b) (0 :: (b ++ a)) := by
    have h := CyclicEq.of_rot hn a.length
    simpa only [rot_append_length, List.cons_append] using h
  have hp : (b ++ a).Perm [1, 2, 3, 4, 5] := by
    exact (List.perm_cons 0).mp (hc.perm.symm.trans hx)
  exact ⟨0 :: (b ++ a), List.mem_map.mpr
    ⟨b ++ a, List.mem_permutations.mpr hp, rfl⟩, hc.symm⟩

theorem canonicalBases6_eq_of_cyclicEq {x y : List Nat}
    (hx : x ∈ canonicalBases6) (hy : y ∈ canonicalBases6)
    (h : CyclicEq x y) : x = y := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  have hz : 0 ∉ a := by
    intro hm
    have hm' := (List.mem_permutations.mp ha).mem_iff.mp hm
    simp at hm'
  have hca : CyclicEq (0 :: a) (a ++ [0]) := by
    have hc := CyclicEq.of_rot (x := 0 :: a) (by simp) 1
    have he : rot (0 :: a) 1 = a ++ [0] := rot_append_length [0] a
    exact Eq.mp (congrArg (fun w => CyclicEq (0 :: a) w) he) hc
  have hcb : CyclicEq (0 :: b) (b ++ [0]) := by
    have hc := CyclicEq.of_rot (x := 0 :: b) (by simp) 1
    have he : rot (0 :: b) 1 = b ++ [0] := rot_append_length [0] b
    exact Eq.mp (congrArg (fun w => CyclicEq (0 :: b) w) he) hc
  have he := Transport.append_satellite_eq_of_cyclicEq hz (hca.symm.trans (h.trans hcb))
  exact congrArg (List.cons 0) he

theorem canonicalBases6_distinct :
    canonicalBases6.Pairwise (fun x y => ¬ CyclicEq x y) := by
  have hn : canonicalBases6.Nodup := by
    apply List.Nodup.map (by intro a b h; exact List.cons.inj h |>.2)
    exact List.nodup_permutations _ (by decide)
  apply hn.imp_of_mem
  intro x y hx hy hne hc
  exact hne (canonicalBases6_eq_of_cyclicEq hx hy hc)

theorem mem_unusedBases6 {x : List Nat} :
    x ∈ unusedBases6 ↔ x ∈ canonicalBases6 ∧ ∀ r ∈ seedRowsNat, ¬ CyclicEq r.base x := by
  simp [unusedBases6]

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem seedRowsNat_length : seedRowsNat.length = 96 := by decide

theorem seedRowsNat_charge : (seedRowsNat.map Row.charge).sum = 48 := by decide

theorem seedRowsNat_basedOn : BasedOn alphabet6 6 seedRowsNat := by
  unfold BasedOn
  decide

theorem seedRowsNat_distinct : DistinctBlocks seedRowsNat := by
  unfold DistinctBlocks
  decide

/-- The canonical 120 cyclic bases leave exactly 24 blocks outside the seeds. -/
theorem unusedBases6_length : unusedBases6.length = 24 := by
  have hp := (List.permutations_perm_permutations' ([1, 2, 3, 4, 5] : List Nat)).map
    (fun tail => 0 :: tail)
  have hf := hp.filter (fun x => decide (∀ r ∈ seedRowsNat, ¬ CyclicEq r.base x))
  rw [show unusedBases6.length = _ from hf.length_eq]
  decide

theorem accountingRows6_length : accountingRows6.length = 120 := by
  simp [accountingRows6, seedRowsNat_length, unusedBases6_length]

theorem unusedBases6_charge :
    ((unusedBases6.map (fun x => (⟨x, 6, 6⟩ : Row Nat))).map Row.charge).sum = 0 := by
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro n hn
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  have hl := canonicalBases6_length (mem_unusedBases6.mp hx).1
  simp [Row.charge, hl]

theorem accountingRows6_charge : (accountingRows6.map Row.charge).sum = 48 := by
  rw [accountingRows6, List.map_append, List.sum_append, seedRowsNat_charge,
    unusedBases6_charge, Nat.add_zero]

theorem accountingRows6_basedOn : BasedOn alphabet6 6 accountingRows6 := by
  intro r hr
  rcases List.mem_append.mp hr with hs | hu
  · exact seedRowsNat_basedOn r hs
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
    have hcan := (mem_unusedBases6.mp hx).1
    have hp := canonicalBases6_perm hcan
    have hl := canonicalBases6_length hcan
    have hnodup : x.Nodup := hp.nodup_iff.mpr (by decide)
    have hsat : 6 ∉ x := by
      intro hm
      have hm' := hp.mem_iff.mp hm
      simp [alphabet6] at hm'
    exact ⟨⟨hnodup, hsat, by change 1 ≤ 6; decide, by simpa using hl.ge⟩,
      hp, rfl, Or.inl hl.symm⟩

theorem accountingRows6_complete : BlockComplete alphabet6 accountingRows6 := by
  intro x hx
  obtain ⟨b, hb, hbx⟩ := canonicalBases6_complete hx
  by_cases hs : ∃ r ∈ seedRowsNat, CyclicEq r.base b
  · obtain ⟨r, hr, hrb⟩ := hs
    exact ⟨r, List.mem_append.mpr (Or.inl hr), hrb.trans hbx⟩
  · have hu : b ∈ unusedBases6 := mem_unusedBases6.mpr ⟨hb, by
      intro r hr hc
      exact hs ⟨r, hr, hc⟩⟩
    exact ⟨⟨b, 6, 6⟩,
      List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨b, hu, rfl⟩)), hbx⟩

theorem accountingRows6_distinct : DistinctBlocks accountingRows6 := by
  apply List.pairwise_append.mpr
  refine ⟨seedRowsNat_distinct, ?_, ?_⟩
  · apply List.pairwise_map.mpr
    exact canonicalBases6_distinct.filter _
  · intro r hr t ht hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact (mem_unusedBases6.mp hb).2 r hr hc

/-- Complete six-symbol block accounting, without an extra closed-trail claim. -/
theorem accountingRows6_certificate :
    unusedBases6.length = 24 ∧ accountingRows6.length = 120 ∧
    (accountingRows6.map Row.charge).sum = 48 ∧
    BasedOn alphabet6 6 accountingRows6 ∧ DistinctBlocks accountingRows6 ∧
    BlockComplete alphabet6 accountingRows6 :=
  ⟨unusedBases6_length, accountingRows6_length, accountingRows6_charge,
    accountingRows6_basedOn, accountingRows6_distinct, accountingRows6_complete⟩

end SuperpermutationUpperBound.Partition.SeedBase
