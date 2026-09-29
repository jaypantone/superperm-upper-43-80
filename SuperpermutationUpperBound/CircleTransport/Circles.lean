import SuperpermutationUpperBound.Completion.Projection
import SuperpermutationUpperBound.Partition.FullCharts

/-! Connector circles and covers of tagged designated trail occurrences.
Repeated representatives are permitted: the list counts selected occurrences. -/
namespace SuperpermutationUpperBound.CircleTransport

open Transport
variable {α ι κ : Type}

/-- A literal vertex of the rotation circle represented by `circle`. -/
def CircleVertex (circle vertex : List α) : Prop := CyclicEq circle vertex

/-- Basic well-formedness does not assume that different selected occurrences
represent different cyclic classes. -/
def CircleFamilyValid (h : Nat) (circles : List (List α)) : Prop :=
  ∀ circle ∈ circles, circle.length = h ∧ circle.Nodup

/-- Optional distinctness, separate from the occurrence-counted cover contract. -/
def DistinctCircleFamily (circles : List (List α)) : Prop :=
  circles.Pairwise (fun a b => ¬ CyclicEq a b)

/-- Every tagged designated object has an incident literal circle vertex. -/
def CoversDesignated (circles : List (List α)) (vertices : ι → List α → Prop) : Prop :=
  ∀ i, ∃ circle ∈ circles, ∃ vertex, vertices i vertex ∧ CircleVertex circle vertex

/-- One selected circle occurrence produces one occurrence per cyclic gap. -/
def circleExtensions (circle : List α) (newOrd : α) : List (List α) :=
  fullBases circle newOrd

def extendCircles (circles : List (List α)) (newOrd : α) : List (List α) :=
  circles.flatMap (fun circle => circleExtensions circle newOrd)

@[simp] theorem circleExtensions_length (circle : List α) (newOrd : α) :
    (circleExtensions circle newOrd).length = circle.length := fullBases_length ..

theorem extendCircles_length (h : Nat) (circles : List (List α)) (newOrd : α)
    (hlen : ∀ circle ∈ circles, circle.length = h) :
    (extendCircles circles newOrd).length = h * circles.length := by
  induction circles with
  | nil => simp [extendCircles]
  | cons circle circles ih =>
    have hc := hlen circle (by simp)
    have ht : ∀ c ∈ circles, c.length = h := fun c hm => hlen c (by simp [hm])
    change (circleExtensions circle newOrd ++ extendCircles circles newOrd).length = _
    rw [List.length_append, circleExtensions_length, hc, ih ht, List.length_cons, Nat.mul_add]
    omega

theorem CircleFamilyValid.extend {h : Nat} {circles : List (List α)}
    (hc : CircleFamilyValid h circles) (newOrd : α)
    (hfresh : ∀ circle ∈ circles, newOrd ∉ circle) :
    CircleFamilyValid (h + 1) (extendCircles circles newOrd) := by
  intro c hm
  obtain ⟨old, hold, hm⟩ := List.mem_flatMap.mp hm
  exact ⟨(fullBases_base_length hm).trans (congrArg (· + 1) (hc old hold).1),
    fullBases_nodup (hc old hold).2 (hfresh old hold) hm⟩

theorem circleExtensions_fresh {circle c : List α} {s newOrd : α}
    (hs : s ∉ circle) (hsw : s ≠ newOrd) (hc : c ∈ circleExtensions circle newOrd) :
    s ∉ c := fullBases_fresh hs hsw hc

/-- All linear insertions into every old circle vertex are actual vertices
of the selected cyclic-gap extensions, including insertion at the final cut. -/
theorem circleVertex_insertLetter {circle vertex : List α} (hc : CircleVertex circle vertex)
    (newOrd : α) {j : Nat} (hj : j ≤ vertex.length) :
    ∃ c ∈ circleExtensions circle newOrd, CircleVertex c (insertLetter vertex newOrd j) := by
  have hn : 0 < vertex.length := List.length_pos_iff.mpr hc.nonempty_right
  have hentry := (insertLetter_cyclicEq_entry vertex newOrd j hj).symm
  have hb : InInsertionBlock newOrd vertex (insertLetter vertex newOrd j) := by
    refine ⟨⟨j % vertex.length, Nat.mod_lt _ hn⟩, ?_⟩
    simpa only [rot_mod] using hentry
  exact (fullBases_cyclicEq_iff_inInsertionBlock circle _ newOrd).mpr
    ((InInsertionBlock.congr_base hc).mpr hb)

/-- The extension operation preserves coverage whenever each new tagged object
has an insertion extension of every old incident vertex of its designated parent. -/
theorem CoversDesignated.extend {circles : List (List α)}
    {oldVertices : ι → List α → Prop} {newVertices : κ → List α → Prop}
    (hcover : CoversDesignated circles oldVertices) (newOrd : α) (parent : κ → ι)
    (hlift : ∀ k v, oldVertices (parent k) v →
      ∃ j, j ≤ v.length ∧ newVertices k (insertLetter v newOrd j)) :
    CoversDesignated (extendCircles circles newOrd) newVertices := by
  intro k
  obtain ⟨circle, hc, v, hv, hcv⟩ := hcover (parent k)
  obtain ⟨j, hj, hvj⟩ := hlift k v hv
  obtain ⟨c, hm, hrot⟩ := circleVertex_insertLetter hcv newOrd hj
  exact ⟨c, List.mem_flatMap.mpr ⟨circle, hc, hm⟩, _, hvj, hrot⟩

/-- Deleting the fresh inserted letter recovers the old cyclic class. -/
theorem circleExtensions_unique_parent [DecidableEq α]
    {a b ca cb : List α} {newOrd : α}
    (ha : ca ∈ circleExtensions a newOrd) (hb : cb ∈ circleExtensions b newOrd)
    (hwa : newOrd ∉ a) (hwb : newOrd ∉ b) (he : CyclicEq ca cb) :
    CyclicEq a b := by
  have hia := (fullBases_cyclicEq_iff_inInsertionBlock a ca newOrd).mp
    ⟨ca, ha, CyclicEq.refl (by have := fullBases_base_length ha; intro hn; simp [hn] at this)⟩
  have hib := (fullBases_cyclicEq_iff_inInsertionBlock b ca newOrd).mp ⟨cb, hb, he.symm⟩
  exact hia.unique_base hib hwa hwb

/-- Changing a representative of an old circle does not change the literal
vertices reached by its selected insertion-extension circles. -/
theorem circleExtensions_congr {a b v : List α} (hab : CyclicEq a b) (newOrd : α) :
    (∃ c ∈ circleExtensions a newOrd, CircleVertex c v) ↔
      (∃ c ∈ circleExtensions b newOrd, CircleVertex c v) := by
  change (∃ c ∈ fullBases a newOrd, CyclicEq c v) ↔
    (∃ c ∈ fullBases b newOrd, CyclicEq c v)
  rw [fullBases_cyclicEq_iff_inInsertionBlock, fullBases_cyclicEq_iff_inInsertionBlock]
  exact InInsertionBlock.congr_base hab

end SuperpermutationUpperBound.CircleTransport
