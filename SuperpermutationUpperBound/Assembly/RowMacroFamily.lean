import SuperpermutationUpperBound.Assembly.ConnectorFamily
import SuperpermutationUpperBound.CircleTransport.Circles
import SuperpermutationUpperBound.CircleTransport.Transport

namespace SuperpermutationUpperBound.RowMacroFamily
variable {I α : Type} {K : Nat}

def edges (rows : I → List (Row α)) (hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = K)
    (i : I) : List (MacroEdge α (K - 3)) :=
  (rows i).attach.map (fun r => MacroEdge.ofRow K r.val (hlen i r.val r.property))

@[simp] theorem edges_length (rows : I → List (Row α))
    (hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = K) (i : I) :
    (edges rows hlen i).length = (rows i).length := by simp [edges]

theorem edges_closed (rows : I → List (Row α))
    (hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = K) (hK : 4 ≤ K)
    (hc : ∀ i, ClosedTrail (rows i)) (hv : ∀ i r, r ∈ rows i → 1 ≤ r.visible) :
    ∀ i, edges rows hlen i ≠ [] ∧
      ∃ v, EdgePath MacroEdge.source MacroEdge.target v (edges rows hlen i) v := by
  intro i
  refine ⟨?_, (hc i).macroEdgePath hK (hlen i) (hv i)⟩
  intro he
  have he := congrArg List.length he
  rw [edges_length, List.length_nil] at he
  exact (hc i).1 (List.length_eq_zero_iff.mp he)

theorem edges_support (rows : I → List (Row α))
    (hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = K) (P : α → Prop)
    (hs : ∀ i r, r ∈ rows i → ∀ a ∈ r.word, P a) :
    ∀ i edge, edge ∈ edges rows hlen i → ∀ a ∈ edge.word, P a := by
  intro i edge he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
  exact hs i r.val r.property

theorem edges_word_mem (rows : I → List (Row α))
    (hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = K) (i : I) (r : Row α)
    (hr : r ∈ rows i) :
    ∃ edge ∈ edges rows hlen i, edge.word = r.word :=
  ⟨MacroEdge.ofRow K r (hlen i r hr), List.mem_map.mpr ⟨⟨r, hr⟩, by simp, rfl⟩, rfl⟩

theorem edges_cost (rows : I → List (Row α))
    (hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = K) (hK : 4 ≤ K)
    (hv : ∀ i r, r ∈ rows i → 1 ≤ r.visible) (i : I) :
    ((edges rows hlen i).map MacroEdge.cost).sum =
      (K + 1) * ((rows i).map Row.visible).sum + (rows i).length := by
  unfold edges
  rw [List.map_map]
  have he : ((rows i).attach.map (fun r =>
      (MacroEdge.ofRow K r.val (hlen i r.val r.property)).cost)) =
      (rows i).map (fun r => (K + 1) * r.visible + 1) := by
    calc
      _ = (rows i).attach.map (fun r => (K + 1) * r.val.visible + 1) := by
        apply List.map_congr_left
        intro r _
        exact MacroEdge.ofRow_cost K r.val _ hK (hv i r.val r.property)
      _ = _ := List.attach_map_val (l := rows i) (f := fun r => (K + 1) * r.visible + 1)
  change (((rows i).attach.map (fun r =>
    (MacroEdge.ofRow K r.val (hlen i r.val r.property)).cost))).sum = _
  rw [he, List.sum_map_add, List.sum_map_mul_left]
  simp

/-- Literal circle-head incidence transfers to the row-word macro edge. -/
theorem edges_cover (rows : I → List (Row α))
    (hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = K)
    (circles : List (List α)) (hc : CircleTransport.CircleFamilyValid (K - 3) circles)
    (hcover : CircleTransport.CoversDesignated circles (fun i => CircleTransport.HeadVertex (rows i))) :
    ∀ i, ∃ c : Fin circles.length, ∃ edge ∈ edges rows hlen i,
      ∃ j, j < K - 3 ∧ edge.source = rot circles[c.val] j := by
  intro i
  obtain ⟨circle, hcircle, v, ⟨r, hr, hv⟩, j, hj⟩ := hcover i
  obtain ⟨c, hclt, hceq⟩ := List.mem_iff_getElem.mp hcircle
  refine ⟨⟨c,hclt⟩, MacroEdge.ofRow K r (hlen i r hr),
    List.mem_map.mpr ⟨⟨r,hr⟩, by simp, rfl⟩, j.val, ?_, ?_⟩
  · simpa only [(hc circle hcircle).1] using j.isLt
  · rw [MacroEdge.ofRow_source, hceq, hv]
    exact hj.symm

end SuperpermutationUpperBound.RowMacroFamily
