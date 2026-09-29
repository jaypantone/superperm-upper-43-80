import SuperpermutationUpperBound.Transport.Successor
import SuperpermutationUpperBound.Transport.FiniteOrbits
import SuperpermutationUpperBound.Transport.Counts
import SuperpermutationUpperBound.Foundation.SupportedWords
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup

namespace SuperpermutationUpperBound.Transport
variable {α β : Type}

/-- Finite labels need not be numbers; every label is used exactly once. -/
theorem finite_labels_path_assembly [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm β) (labels : List β) (hlabels : labels.Nodup)
    (hcomplete : ∀ i, i ∈ labels) (paths : β → List (Row α))
    (hpaths : ∀ i, paths i ≠ [])
    (hinternal : ∀ i, RowTrailCompatible ((paths i).head (hpaths i)) (paths i).tail)
    (hboundary : ∀ i, ((paths i).getLast (hpaths i)).Compatible
      ((paths (σ i)).head (hpaths (σ i)))) :
    ∃ trails : List (List (Row α)), (∀ trail ∈ trails, ClosedTrail trail) ∧
      trails.flatten.Perm (labels.flatMap paths) := by
  obtain ⟨orbits, hperiods, hpartition⟩ :=
    invariant_finset_orbit_partition σ Finset.univ (by simp)
  have hp : Finset.univ.toList.Perm labels := by
    apply (List.perm_ext_iff_of_nodup Finset.univ.nodup_toList hlabels).mpr
    intro i
    simp [hcomplete i]
  obtain ⟨trails, hc, hp, _⟩ := assembly_of_orbit_partition paths σ hpaths
    hinternal hboundary labels orbits hperiods (hpartition.trans hp)
  exact ⟨trails, hc, hp⟩

/-- Closed-trail compatibility at each cyclic occurrence index. -/
theorem closedTrail_getElem_compatible {rs : List (Row α)} (hc : ClosedTrail rs)
    (i : Fin rs.length) :
    (rs[i.val]).Compatible (rs[(i.val + 1) % rs.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt))) := by
  have hp : (rs[i.val], (rot rs 1)[i.val]'(by simpa using i.isLt)) ∈ rs.zip (rot rs 1) := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simpa using i.isLt, ?_⟩
    simp
  have h := hc.2 _ hp
  rw [getElem_rot] at h
  simpa only [Nat.add_comm 1 i.val] using h

theorem finRange_map_getElem (rs : List β) :
    (List.finRange rs.length).map (fun i => rs[i.val]) = rs := by
  simp [List.finRange, Function.comp_def]

/-- A permutation of each sublist gives a permutation of their concatenation. -/
theorem flatMap_perm_of_pointwise (xs : List β) (f g : β → List α)
    (h : ∀ x ∈ xs, (f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => exact .refl _
  | cons a xs ih =>
    simp only [List.flatMap_cons]
    exact (h a (by simp)).append (ih (fun x hx => h x (by simp [hx])))

/-- The occurrence inventory of all insertion-port paths. -/
theorem portPaths_inventory (rs : List (Row α)) (z : α) (n : Nat)
    (hn : 3 ≤ n) (hlen : ∀ r ∈ rs, r.base.length = n) :
    ((List.finRange rs.length).flatMap (fun i =>
      (List.finRange (n - 1)).flatMap (fun p => portPath rs[i.val] z p.val))).Perm
      (packingRows rs z) := by
  have hp : ((List.finRange rs.length).flatMap (fun i =>
      (List.finRange (n - 1)).flatMap (fun p => portPath rs[i.val] z p.val))).Perm
      ((List.finRange rs.length).flatMap (fun i => rows rs[i.val] z)) := by
    apply flatMap_perm_of_pointwise
    intro i _
    have hi := hlen rs[i.val] (List.getElem_mem _)
    have he := portPaths_flatten_perm rs[i.val] z (by omega)
    rw [hi] at he
    have heq : (List.finRange (n - 1)).flatMap (fun p => portPath rs[i.val] z p.val) =
        ((List.range (n - 1)).map (portPath rs[i.val] z)).flatten := by
      rw [← map_val_finRange (n - 1), List.map_map]
      rfl
    rw [heq]
    exact he
  refine hp.trans ?_
  have heq := congrArg (fun xs => xs.flatMap (fun r => rows r z)) (finRange_map_getElem rs)
  rw [List.flatMap_map] at heq
  exact List.Perm.of_eq heq

theorem product_portPaths_inventory (rs : List (Row α)) (z : α) (n : Nat)
    (hn : 3 ≤ n) (hlen : ∀ r ∈ rs, r.base.length = n) :
    (((List.finRange rs.length).product (List.finRange (n - 1))).flatMap
      (fun ip => portPath rs[ip.1.val] z ip.2.val)).Perm (packingRows rs z) := by
  simpa only [List.product, List.flatMap_assoc, List.flatMap_map, Function.comp_def]
    using portPaths_inventory rs z n hn hlen

/-- Every full/deficit-two closed trail transports to literal closed trails.
The conclusion preserves all row occurrences, including equal row values. -/
theorem transport_closedTrail {rs : List (Row α)} (z : α) (n : Nat)
    (hn : 3 ≤ n) (hc : ClosedTrail rs)
    (hlen : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ∃ trails : List (List (Row α)), (∀ trail ∈ trails, ClosedTrail trail) ∧
      trails.flatten.Perm (packingRows rs z) := by
  have hR : 0 < rs.length := List.length_pos_iff.mpr hc.1
  let σ := rowPortSuccessor hR n hn (fun i => rs[i.val])
  let labels := (List.finRange rs.length).product (List.finRange (n - 1))
  let paths := fun ip : Fin rs.length × Fin (n - 1) => portPath rs[ip.1.val] z ip.2.val
  have hi (i : Fin rs.length) : (rs[i.val]).base.length = n :=
    hlen _ (List.getElem_mem _)
  have hk (i : Fin rs.length) := hkind _ (List.getElem_mem (l := rs) (n := i.val) i.isLt)
  have hne : ∀ ip, paths ip ≠ [] := fun ip => portPath_nonempty _ _ _
  have hinternal : ∀ ip, RowTrailCompatible ((paths ip).head (hne ip)) (paths ip).tail := by
    intro ip
    exact portPath_internal _ _ _ (by rw [hi]; omega)
  have hboundary : ∀ ip, ((paths ip).getLast (hne ip)).Compatible
      ((paths (σ ip)).head (hne (σ ip))) := by
    intro ip
    change ((portPath rs[ip.1.val] z ip.2.val).getLast _).tail =
      ((portPath rs[(σ ip).1.val] z (σ ip).2.val).head _).head
    rw [portPath_last_tail z (by rw [hi]; exact hn) (hk ip.1) (by rw [hi]; exact ip.2.isLt),
      portPath_head z (by rw [hi]; exact hn) (hk (σ ip).1)
        (by rw [hi]; exact (σ ip).2.isLt)]
    have hs : (σ ip).2.val = portTarget rs[ip.1.val] ip.2.val :=
      rowPortSuccessor_snd_val hR n hn _ hi ip
    rw [hs]
    have hrow := closedTrail_getElem_compatible hc ip.1
    have hf : (σ ip).1.val = (ip.1.val + 1) % rs.length :=
      rowPortSuccessor_fst_val hR n hn _ ip
    simp only [hf]
    rw [hrow]
  obtain ⟨trails, hclosed, hperm⟩ := finite_labels_path_assembly σ labels
    ((nodup_finRange _).product (nodup_finRange _))
    (by
      intro ip
      exact List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩) paths hne hinternal hboundary
  exact ⟨trails, hclosed, hperm.trans (product_portPaths_inventory rs z n hn hlen)⟩

end SuperpermutationUpperBound.Transport
