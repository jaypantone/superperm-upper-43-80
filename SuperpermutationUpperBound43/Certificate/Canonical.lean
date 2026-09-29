import SuperpermutationUpperBound.Partition.SprintBase
import Mathlib.Data.List.Permutation

/-! Canonical cyclic bases and the bridge from a finite inventory to the
semantic partition hypotheses. No concrete new row family occurs here. -/
namespace SuperpermutationUpperBound43.Certificate

open SuperpermutationUpperBound

def canonical (x : List Nat) : List Nat := rot x (x.idxOf 0)

def canonicalBases : List (List Nat) :=
  (List.permutations' [1, 2, 3, 4, 5, 6, 7, 8]).map (List.cons 0)

theorem alphabet9_perm_standard :
    Partition.SprintBase.alphabet9.Perm [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide

theorem canonical_cyclicEq {x : List Nat} (hx : x ≠ []) :
    CyclicEq x (canonical x) :=
  CyclicEq.of_rot hx (x.idxOf 0)

theorem canonicalBases_perm {x : List Nat} (hx : x ∈ canonicalBases) :
    x.Perm Partition.SprintBase.alphabet9 := by
  obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hx
  exact ((List.mem_permutations'.mp ht).cons 0).trans alphabet9_perm_standard.symm

theorem canonicalBases_length {x : List Nat} (hx : x ∈ canonicalBases) :
    x.length = 9 :=
  (canonicalBases_perm hx).length_eq

theorem canonicalBases_complete {x : List Nat}
    (hx : x.Perm Partition.SprintBase.alphabet9) :
    ∃ b ∈ canonicalBases, CyclicEq b x := by
  have hx' := hx.trans alphabet9_perm_standard
  have hzero : 0 ∈ x := hx'.mem_iff.mpr (by decide)
  obtain ⟨a, b, rfl, _⟩ := List.eq_append_cons_of_mem hzero
  have hn : a ++ 0 :: b ≠ [] := by simp
  have hc : CyclicEq (a ++ 0 :: b) (0 :: (b ++ a)) := by
    have h := CyclicEq.of_rot hn a.length
    simpa only [rot_append_length, List.cons_append] using h
  have hp : (b ++ a).Perm [1, 2, 3, 4, 5, 6, 7, 8] :=
    (List.perm_cons 0).mp (hc.perm.symm.trans hx')
  exact ⟨0 :: (b ++ a), List.mem_map.mpr
    ⟨b ++ a, List.mem_permutations'.mpr hp, rfl⟩, hc.symm⟩

theorem canonicalBases_eq_of_cyclicEq {x y : List Nat}
    (hx : x ∈ canonicalBases) (hy : y ∈ canonicalBases)
    (h : CyclicEq x y) : x = y := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  have hz : 0 ∉ a := by
    intro hm
    have hm' := (List.mem_permutations'.mp ha).mem_iff.mp hm
    simp at hm'
  have hca : CyclicEq (0 :: a) (a ++ [0]) := by
    have hc := CyclicEq.of_rot (x := 0 :: a) (by simp) 1
    have he : rot (0 :: a) 1 = a ++ [0] := rot_append_length [0] a
    exact Eq.mp (congrArg (fun w => CyclicEq (0 :: a) w) he) hc
  have hcb : CyclicEq (0 :: b) (b ++ [0]) := by
    have hc := CyclicEq.of_rot (x := 0 :: b) (by simp) 1
    have he : rot (0 :: b) 1 = b ++ [0] := rot_append_length [0] b
    exact Eq.mp (congrArg (fun w => CyclicEq (0 :: b) w) he) hc
  have he := Transport.append_satellite_eq_of_cyclicEq hz
    (hca.symm.trans (h.trans hcb))
  exact congrArg (List.cons 0) he

theorem canonicalBases_nodup : canonicalBases.Nodup := by
  apply List.Nodup.map (by intro a b h; exact List.cons.inj h |>.2)
  exact (List.permutations_perm_permutations' _).nodup_iff.mp
    (List.nodup_permutations _ (by decide))

theorem canonicalBases_distinct :
    canonicalBases.Pairwise (fun x y => ¬ CyclicEq x y) := by
  apply canonicalBases_nodup.imp_of_mem
  intro x y hx hy hne hc
  exact hne (canonicalBases_eq_of_cyclicEq hx hy hc)

theorem row_base_nonempty {rs : List (Row Nat)}
    (hb : BasedOn Partition.SprintBase.alphabet9 9 rs) {r : Row Nat} (hr : r ∈ rs) :
    r.base ≠ [] := by
  have hl : r.base.length = 9 := (hb r hr).2.1.length_eq
  intro he
  rw [he] at hl
  contradiction

theorem complete_of_canonical_inventory {rs : List (Row Nat)}
    (hb : BasedOn Partition.SprintBase.alphabet9 9 rs)
    (hi : (rs.map (fun r => canonical r.base)).Perm canonicalBases) :
    BlockComplete Partition.SprintBase.alphabet9 rs := by
  intro x hx
  obtain ⟨b, hbcan, hbx⟩ := canonicalBases_complete hx
  obtain ⟨r, hr, he⟩ := List.mem_map.mp (hi.mem_iff.mpr hbcan)
  have hrc : CyclicEq r.base b := he ▸ canonical_cyclicEq (row_base_nonempty hb hr)
  exact ⟨r, hr, hrc.trans hbx⟩

theorem distinct_of_canonical_inventory {rs : List (Row Nat)}
    (hb : BasedOn Partition.SprintBase.alphabet9 9 rs)
    (hi : (rs.map (fun r => canonical r.base)).Perm canonicalBases) :
    DistinctBlocks rs := by
  have hn : (rs.map (fun r => canonical r.base)).Nodup :=
    hi.nodup_iff.mpr canonicalBases_nodup
  have hp : rs.Pairwise (fun r t => canonical r.base ≠ canonical t.base) :=
    List.pairwise_map.mp hn
  apply hp.imp_of_mem
  intro r t hr ht hne hcyc
  have hrc := canonical_cyclicEq (row_base_nonempty hb hr)
  have htc := canonical_cyclicEq (row_base_nonempty hb ht)
  have hrmem : canonical r.base ∈ canonicalBases :=
    hi.mem_iff.mp (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have htmem : canonical t.base ∈ canonicalBases :=
    hi.mem_iff.mp (List.mem_map.mpr ⟨t, ht, rfl⟩)
  exact hne (canonicalBases_eq_of_cyclicEq hrmem htmem
    (hrc.symm.trans (hcyc.trans htc)))

theorem partition_of_canonical_inventory {rs : List (Row Nat)}
    (hb : BasedOn Partition.SprintBase.alphabet9 9 rs)
    (hi : (rs.map (fun r => canonical r.base)).Perm canonicalBases) :
    BlockComplete Partition.SprintBase.alphabet9 rs ∧ DistinctBlocks rs :=
  ⟨complete_of_canonical_inventory hb hi, distinct_of_canonical_inventory hb hi⟩

end SuperpermutationUpperBound43.Certificate
