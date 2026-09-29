import SuperpermutationUpperBound.Transport.Closed
import SuperpermutationUpperBound.Certificates.NatSeeds
import SuperpermutationUpperBound.Partition.AllSizes

namespace SuperpermutationUpperBound
variable {α : Type}

/-- A list of closed trails using precisely the given row occurrences. -/
def HasClosedDecomposition (rs : List (Row α)) : Prop :=
  ∃ trails : List (List (Row α)), (∀ trail ∈ trails, ClosedTrail trail) ∧
    trails.flatten.Perm rs

theorem HasClosedDecomposition.perm {rs ts : List (Row α)}
    (h : HasClosedDecomposition rs) (hp : rs.Perm ts) : HasClosedDecomposition ts := by
  obtain ⟨trails, hc, hr⟩ := h
  exact ⟨trails, hc, hr.trans hp⟩

theorem HasClosedDecomposition.append {rs ts : List (Row α)}
    (hr : HasClosedDecomposition rs) (ht : HasClosedDecomposition ts) :
    HasClosedDecomposition (rs ++ ts) := by
  obtain ⟨left, hl, hpl⟩ := hr
  obtain ⟨right, hr, hpr⟩ := ht
  refine ⟨left ++ right, ?_, ?_⟩
  · intro trail htrail
    rcases List.mem_append.mp htrail with h | h
    · exact hl trail h
    · exact hr trail h
  · simpa only [List.flatten_append] using hpl.append hpr

theorem HasClosedDecomposition.flatMap (trails : List (List (Row α)))
    (f : Row α → List (Row α))
    (h : ∀ trail ∈ trails, HasClosedDecomposition (trail.flatMap f)) :
    HasClosedDecomposition (trails.flatten.flatMap f) := by
  induction trails with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons trail trails ih =>
    simpa only [List.flatten_cons, List.flatMap_append] using
      (h trail (by simp)).append (ih (fun t ht => h t (by simp [ht])))

/-- Transport preserves the existence of an exact closed decomposition. -/
theorem HasClosedDecomposition.transport {rs : List (Row α)}
    (h : HasClosedDecomposition rs) (z : α) (n : Nat) (hn : 3 ≤ n)
    (hlen : ∀ r ∈ rs, r.base.length = n)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    HasClosedDecomposition (Transport.packingRows rs z) := by
  obtain ⟨trails, hc, hp⟩ := h
  have hlocal : ∀ trail ∈ trails,
      HasClosedDecomposition (trail.flatMap (fun r => Transport.rows r z)) := by
    intro trail ht
    apply Transport.transport_closedTrail z n hn (hc trail ht)
    · intro r hr
      exact hlen r (hp.mem_iff.mp (List.mem_flatten.mpr ⟨trail, ht, hr⟩))
    · intro r hr
      exact hkind r (hp.mem_iff.mp (List.mem_flatten.mpr ⟨trail, ht, hr⟩))
  exact (HasClosedDecomposition.flatMap trails _ hlocal).perm (hp.flatMap_right _)

namespace Partition

theorem originalSeven_closedDecomposition : HasClosedDecomposition OriginalSeven.rows7 := by
  have hs : HasClosedDecomposition SeedBase.seedRowsNat :=
    ⟨Certificates.NatSeeds.trails, Certificates.NatSeeds.trails_closed,
      List.Perm.of_eq Certificates.NatSeeds.trails_flatten_eq_seedRowsNat⟩
  have hm : HasClosedDecomposition OriginalSeven.mixedRows7 := by
    apply hs.transport 7 6 (by decide)
    · intro r hr
      exact (SeedBase.seedRowsNat_basedOn r hr).2.1.length_eq
    · intro r hr
      exact (SeedBase.seedRowsNat_basedOn r hr).2.2.2
  have hf : HasClosedDecomposition OriginalSeven.chartRows7 :=
    ⟨OriginalSeven.fullCharts7, OriginalSeven.fullCharts7_closed, .refl _⟩
  exact hm.append hf

/-- At every size, the original block partition has an exact closed-trail
realization. No component count or run invariant is asserted here. -/
theorem blockRows_closedDecomposition (k : Nat) : HasClosedDecomposition (blockRows k) := by
  induction k with
  | zero => exact originalSeven_closedDecomposition
  | succ k ih =>
    apply ih.transport (k + 8) (k + 7) (by omega)
    · intro r hr
      exact (blockRows_basedOn k r hr).2.1.length_eq.trans (blockAlphabet_length k)
    · intro r hr
      exact (blockRows_basedOn k r hr).2.2.2

end Partition
end SuperpermutationUpperBound
