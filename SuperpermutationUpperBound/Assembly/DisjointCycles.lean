import SuperpermutationUpperBound.Assembly.BalancedGraph

namespace SuperpermutationUpperBound
variable {E V : Type}

/-- Two edge lists have no common incident vertex. -/
def DisjointIncidence (src dst : E → V) (xs ys : List E) : Prop :=
  ∀ v, ¬ (EdgeIncident src dst xs v ∧ EdgeIncident src dst ys v)

def ClosedCycles (src dst : E → V) (cycles : List (List E)) : Prop :=
  ∀ es ∈ cycles, es ≠ [] ∧ ∃ v, EdgePath src dst v es v

/-- If closed cycles are not pairwise disjoint at their vertices, a splice
reduces their number and preserves the complete edge inventory. -/
theorem closed_cycles_disjoint_or_reduce (src dst : E → V) (cycles : List (List E))
    (hc : ClosedCycles src dst cycles) :
    cycles.Pairwise (DisjointIncidence src dst) ∨
    ∃ reduced, ClosedCycles src dst reduced ∧ reduced.flatten.Perm cycles.flatten ∧
      reduced.length < cycles.length := by
  classical
  induction cycles with
  | nil => exact Or.inl (by simp)
  | cons first rest ih =>
    have hr : ClosedCycles src dst rest := fun es h => hc es (by simp [h])
    rcases ih hr with hd | ⟨reduced, hred, hp, hn⟩
    · by_cases hfirst : ∀ es ∈ rest, DisjointIncidence src dst first es
      · exact Or.inl (List.pairwise_cons.mpr ⟨hfirst, hd⟩)
      · push Not at hfirst
        obtain ⟨second, hsecond, hshare⟩ := hfirst
        simp only [DisjointIncidence, not_forall, not_not] at hshare
        obtain ⟨v, hvf, hvs⟩ := hshare
        obtain ⟨_, a, ha⟩ := hc first (by simp)
        obtain ⟨_, b, hb⟩ := hr second hsecond
        obtain ⟨joined, hj, hjp, hjn⟩ := ha.splice_at_shared_vertex hb hvf hvs
        refine Or.inr ⟨joined :: rest.erase second, ?_, ?_, ?_⟩
        · intro es hes
          rcases List.mem_cons.mp hes with rfl | hes
          · exact ⟨hjn, v, hj⟩
          · exact hr es (List.mem_of_mem_erase hes)
        · have hinv := (List.perm_cons_erase hsecond).flatten
          simp only [List.flatten_cons] at hinv ⊢
          exact (hjp.append_right _).trans (by
            simpa only [List.append_assoc] using (hinv.symm.append_left first))
        · have hl := List.length_erase_add_one hsecond
          simp only [List.length_cons]
          omega
    · refine Or.inr ⟨first :: reduced, ?_, ?_, ?_⟩
      · intro es hes
        rcases List.mem_cons.mp hes with rfl | hes
        · exact hc es (by simp)
        · exact hred es hes
      · simpa only [List.flatten_cons] using hp.append_left first
      · simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hn

/-- Every finite closed-cycle family can be spliced into vertex-disjoint
closed cycles. Edge labels and their multiplicities are preserved. -/
theorem closed_cycles_disjoint_decomposition (src dst : E → V) (cycles : List (List E))
    (hc : ClosedCycles src dst cycles) :
    ∃ result, ClosedCycles src dst result ∧ result.flatten.Perm cycles.flatten ∧
      result.Pairwise (DisjointIncidence src dst) := by
  classical
  let P (n : Nat) := ∃ cs : List (List E), ClosedCycles src dst cs ∧
    cs.flatten.Perm cycles.flatten ∧ cs.length = n
  have hex : ∃ n, P n := ⟨cycles.length, cycles, hc, List.Perm.refl _, rfl⟩
  obtain ⟨cs, hcs, hp, hlen⟩ := Nat.find_spec hex
  rcases closed_cycles_disjoint_or_reduce src dst cs hcs with hd | ⟨rs, hrs, hrp, hrlen⟩
  · exact ⟨cs, hcs, hp, hd⟩
  · have hmin := Nat.find_min' hex (show P rs.length from ⟨rs, hrs, hrp.trans hp, rfl⟩)
    omega

/-- There are at most as many nonempty vertex-disjoint cycles as vertices. -/
theorem disjoint_closed_cycles_length_le [Fintype V] (src dst : E → V)
    (cycles : List (List E)) (hc : ClosedCycles src dst cycles)
    (hd : cycles.Pairwise (DisjointIncidence src dst)) : cycles.length ≤ Fintype.card V := by
  classical
  have he : ∀ i : Fin cycles.length, ∃ e, e ∈ cycles[i.val] := by
    intro i
    exact List.exists_mem_of_ne_nil _ (hc _ (List.getElem_mem i.isLt)).1
  choose edge hedge using he
  let f : Fin cycles.length → V := fun i => src (edge i)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hlt : i.val < j.val ∨ j.val < i.val := by
      have : i.val ≠ j.val := fun h => hne (Fin.ext h)
      omega
    have hi : EdgeIncident src dst cycles[i.val] (f i) := ⟨edge i, hedge i, Or.inl rfl⟩
    have hj : EdgeIncident src dst cycles[j.val] (f i) := ⟨edge j, hedge j, Or.inl hij.symm⟩
    rcases hlt with hlt | hlt
    · exact (List.pairwise_iff_getElem.mp hd i.val j.val i.isLt j.isLt hlt) (f i) ⟨hi, hj⟩
    · exact (List.pairwise_iff_getElem.mp hd j.val i.val j.isLt i.isLt hlt) (f i) ⟨hj, hi⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Balanced finite directed multigraphs admit a cycle decomposition whose
nonempty cycles have disjoint vertex sets, hence at most `card V` cycles. -/
theorem balanced_graph_disjoint_cycles [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
    (src dst : E → V) (hb : BalancedDegrees src dst) :
    ∃ cycles : List (List E), ClosedCycles src dst cycles ∧
      cycles.flatten.Perm Finset.univ.toList ∧
      cycles.Pairwise (DisjointIncidence src dst) ∧ cycles.length ≤ Fintype.card V := by
  obtain ⟨cs, hc, hp⟩ := balanced_graph_cycle_decomposition src dst hb
  obtain ⟨rs, hr, hi, hd⟩ := closed_cycles_disjoint_decomposition src dst cs hc
  exact ⟨rs, hr, hi.trans hp, hd, disjoint_closed_cycles_length_le src dst rs hr hd⟩

end SuperpermutationUpperBound
