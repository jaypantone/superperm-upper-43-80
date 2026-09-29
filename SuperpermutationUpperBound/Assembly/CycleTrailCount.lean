import SuperpermutationUpperBound.Assembly.RemoveEdges

namespace SuperpermutationUpperBound
variable {E V : Type}

/-- Removing edges from a family of closed cycles costs at most one trail
per removed occurrence, plus one per cycle containing no removed edge. -/
theorem closed_cycles_remove_edges (src dst : E → V) (keep : E → Bool)
    (cycles : List (List E)) (hc : ClosedCycles src dst cycles) :
    ∃ trails, DirectedTrails src dst trails ∧
      trails.flatten.Perm (cycles.flatten.filter keep) ∧
      trails.length ≤ cycles.flatten.countP (fun e => !(keep e)) +
        (cycles.filter (fun es => es.all keep)).length := by
  induction cycles with
  | nil => exact ⟨[], by simp [DirectedTrails], by simp, by simp⟩
  | cons first rest ih =>
    obtain ⟨tail, ht, hi, hl⟩ := ih (fun es h => hc es (by simp [h]))
    obtain ⟨hn, a, hp⟩ := hc first (by simp)
    by_cases hk : first.all keep = true
    · have hfilter : first.filter keep = first := List.filter_eq_self.mpr (by simpa using hk)
      have hcount : first.countP (fun e => !(keep e)) = 0 := by
        apply List.countP_eq_zero.mpr
        intro e he
        have h := List.all_eq_true.mp hk e he
        simp [h]
      refine ⟨first :: tail, ?_, ?_, ?_⟩
      · intro es hes
        rcases List.mem_cons.mp hes with rfl | hes
        · exact ⟨hn, a, a, hp⟩
        · exact ht es hes
      · simpa [List.flatten_cons, List.filter_append, hfilter] using hi.append_left first
      · simpa [List.flatten_cons, List.countP_append, List.filter_cons, hk, hcount,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.add_le_add_right hl 1
    · have hex : ∃ e ∈ first, keep e = false := by
        simpa only [List.all_eq_true, not_forall, Bool.not_eq_true, exists_prop] using hk
      obtain ⟨e, he, hekeep⟩ := hex
      obtain ⟨runs, hr, hri, hrl⟩ := hp.remove_edges_closed keep he hekeep
      refine ⟨runs ++ tail, ?_, ?_, ?_⟩
      · intro es hes
        rcases List.mem_append.mp hes with hes | hes
        · exact hr es hes
        · exact ht es hes
      · simpa only [List.flatten_append, List.flatten_cons, List.filter_append] using hri.append hi
      · have hh := Nat.add_le_add hrl hl
        simpa [List.length_append, List.flatten_cons, List.countP_append,
          List.filter_cons, hk, Nat.add_assoc] using hh

/-- Selecting one incident vertex in a fixed finite set bounds a family of
vertex-disjoint nonempty cycles by the size of that set. -/
theorem disjoint_cycles_length_le_finset [DecidableEq V] (src dst : E → V)
    (cycles : List (List E)) (Z : Finset V)
    (hd : cycles.Pairwise (DisjointIncidence src dst))
    (hz : ∀ es ∈ cycles, ∃ v ∈ Z, EdgeIncident src dst es v) :
    cycles.length ≤ Z.card := by
  classical
  have hv : ∀ i : Fin cycles.length, ∃ v : Z, EdgeIncident src dst cycles[i.val] v := by
    intro i
    obtain ⟨v, hZ, hi⟩ := hz _ (List.getElem_mem i.isLt)
    exact ⟨⟨v, hZ⟩, hi⟩
  choose f hf using hv
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hlt : i.val < j.val ∨ j.val < i.val := by omega
    have hi := hf i
    have hj : EdgeIncident src dst cycles[j.val] (f i) := by rw [hij]; exact hf j
    rcases hlt with hlt | hlt
    · exact (List.pairwise_iff_getElem.mp hd _ _ i.isLt j.isLt hlt) (f i) ⟨hi, hj⟩
    · exact (List.pairwise_iff_getElem.mp hd _ _ j.isLt i.isLt hlt) (f i) ⟨hj, hi⟩
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hinj

end SuperpermutationUpperBound

namespace SuperpermutationUpperBound
variable {E V : Type}

/-- Incidence in a pairwise vertex-disjoint family identifies its cycle. -/
theorem disjoint_cycles_common_vertex {src dst : E → V} {cycles : List (List E)}
    (hd : cycles.Pairwise (DisjointIncidence src dst)) {xs ys : List E}
    (hx : xs ∈ cycles) (hy : ys ∈ cycles) {v : V}
    (hvx : EdgeIncident src dst xs v) (hvy : EdgeIncident src dst ys v) : xs = ys := by
  induction cycles with
  | nil => simp at hx
  | cons first rest ih =>
    obtain ⟨hf, hr⟩ := List.pairwise_cons.mp hd
    rcases List.mem_cons.mp hx with hxf | hxr
    · subst xs
      rcases List.mem_cons.mp hy with hyf | hyr
      · exact hyf.symm
      · exact False.elim (hf ys hyr v ⟨hvx, hvy⟩)
    · rcases List.mem_cons.mp hy with hyf | hyr
      · subst ys
        exact False.elim (hf xs hxr v ⟨hvy, hvx⟩)
      · exact ih hr hxr hyr


/-- A cycle containing no marked edge cannot meet a vertex that is incident
to a marked edge elsewhere in a complete disjoint-cycle decomposition. -/
theorem retained_cycle_vertices {src dst : E → V} {cycles : List (List E)}
    (keep : E → Bool) (Z : Finset V)
    (hd : cycles.Pairwise (DisjointIncidence src dst))
    (hall : ∀ e, ∃ es ∈ cycles, e ∈ es)
    (hmark : ∀ v, v ∉ Z → ∃ e, keep e = false ∧ (src e = v ∨ dst e = v))
    {es : List E} (hes : es ∈ cycles) (hk : es.all keep = true)
    {v : V} (hv : EdgeIncident src dst es v) : v ∈ Z := by
  classical
  by_contra hz
  obtain ⟨e, he, hev⟩ := hmark v hz
  obtain ⟨other, ho, heo⟩ := hall e
  have hsame := disjoint_cycles_common_vertex hd hes ho hv ⟨e, heo, hev⟩
  have hem : e ∈ es := hsame ▸ heo
  have hkeep := List.all_eq_true.mp hk e hem
  simp [he] at hkeep

/-- If every vertex outside `Z` meets a marked edge, removing marked edges
from disjoint closed cycles leaves at most `cuts + card Z` directed trails. -/
theorem disjoint_cycles_remove_edges_bound [DecidableEq V]
    (src dst : E → V) (keep : E → Bool) (Z : Finset V)
    (cycles : List (List E)) (hc : ClosedCycles src dst cycles)
    (hd : cycles.Pairwise (DisjointIncidence src dst))
    (hall : ∀ e, ∃ es ∈ cycles, e ∈ es)
    (hmark : ∀ v, v ∉ Z → ∃ e, keep e = false ∧ (src e = v ∨ dst e = v)) :
    ∃ trails, DirectedTrails src dst trails ∧
      trails.flatten.Perm (cycles.flatten.filter keep) ∧
      trails.length ≤ cycles.flatten.countP (fun e => !(keep e)) + Z.card := by
  obtain ⟨ts, ht, hi, hl⟩ := closed_cycles_remove_edges src dst keep cycles hc
  have hfilter := hd.filter (fun es => es.all keep)
  have hz : ∀ es ∈ cycles.filter (fun es => es.all keep),
      ∃ v ∈ Z, EdgeIncident src dst es v := by
    intro es hes
    obtain ⟨hmem, hkeep⟩ := List.mem_filter.mp hes
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil es (hc es hmem).1
    have hv : EdgeIncident src dst es (src e) := ⟨e, he, Or.inl rfl⟩
    exact ⟨src e, retained_cycle_vertices keep Z hd hall hmark hmem hkeep hv, hv⟩
  have hlen := disjoint_cycles_length_le_finset src dst _ Z hfilter hz
  exact ⟨ts, ht, hi, hl.trans (Nat.add_le_add_left hlen _)⟩

/-- A family of nonempty trails never has more trails than edge occurrences. -/
theorem DirectedTrails.length_le_flatten {src dst : E → V} {trails : List (List E)}
    (ht : DirectedTrails src dst trails) : trails.length ≤ trails.flatten.length := by
  induction trails with
  | nil => simp
  | cons first rest ih =>
    have hn := (ht first (by simp)).1
    have hl : 1 ≤ first.length := by
      have h := List.length_pos_iff.mpr hn
      omega
    have hr := ih (fun es hes => ht es (by simp [hes]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

end SuperpermutationUpperBound
