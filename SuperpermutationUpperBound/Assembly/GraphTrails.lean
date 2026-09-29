import SuperpermutationUpperBound.Assembly.CycleTrailCount
import SuperpermutationUpperBound.Assembly.BalancingEdges

namespace SuperpermutationUpperBound
variable {E D V : Type}

/-- Erase the sum tag from an all-left directed path. -/
theorem EdgePath.left_labels {src dst : E → V} {extraSrc extraDst : D → V}
    {a b : V} {es : List (E ⊕ D)}
    (hp : EdgePath (Sum.elim src extraSrc) (Sum.elim dst extraDst) a es b)
    (hl : ∀ e ∈ es, e.isLeft = true) :
    EdgePath src dst a (es.filterMap Sum.getLeft?) b ∧
      (es.filterMap Sum.getLeft?).map Sum.inl = es := by
  induction hp with
  | nil a => exact ⟨.nil a, rfl⟩
  | @cons a b e es he ht ih =>
    obtain ⟨hr, hi⟩ := ih (fun f hf => hl f (by simp [hf]))
    cases e with
    | inl e => exact ⟨.cons he hr, by simpa using congrArg (List.cons (Sum.inl e)) hi⟩
    | inr d => have h := hl (.inr d) (by simp); simp at h

/-- A convenient occurrence enumeration for a disjoint sum of finite types. -/
theorem sum_univ_list_perm [Fintype E] [Fintype D] [DecidableEq E] [DecidableEq D] :
    (Finset.univ.toList : List (E ⊕ D)).Perm
      ((Finset.univ.toList : List E).map Sum.inl ++
        (Finset.univ.toList : List D).map Sum.inr) := by
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) ?_).mpr
  · intro e
    cases e <;> simp
  · apply List.nodup_append.mpr
    refine ⟨(Finset.nodup_toList _).map Sum.inl_injective,
      (Finset.nodup_toList _).map Sum.inr_injective, ?_⟩
    intro x hx y hy hxy
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hy
    cases hxy

/-- Every finite directed multigraph with imbalance at most two decomposes
into at most one nonempty directed trail per vertex and per edge. -/
theorem directed_graph_trail_bound [Fintype E] [Fintype V] [DecidableEq V]
    (src dst : E → V) (hb : ∀ v, |degreeImbalance src dst v| ≤ 2) :
    ∃ trails : List (List E), DirectedTrails src dst trails ∧
      trails.flatten.Perm Finset.univ.toList ∧
      trails.length ≤ min (Fintype.card E) (Fintype.card V) := by
  classical
  let D := BalancingDummy src dst
  let sr := balancedSource src dst
  let dt := balancedTarget src dst
  let Z : Finset V := Finset.univ.filter (fun v => degreeImbalance src dst v = 0)
  obtain ⟨cycles, hc, hi, hd, _⟩ := balanced_graph_disjoint_cycles sr dt
    (balancing_extension_balanced src dst)
  have hall : ∀ e, ∃ es ∈ cycles, e ∈ es := by
    intro e
    exact List.mem_flatten.mp (hi.mem_iff.mpr (by simp))
  have hmark : ∀ v, v ∉ Z → ∃ e : E ⊕ D, e.isLeft = false ∧ (sr e = v ∨ dt e = v) := by
    intro v hv
    have hn : degreeImbalance src dst v ≠ 0 := by simpa [Z] using hv
    obtain ⟨d, hd⟩ := (nonzero_iff_dummy_incident src dst v).mp hn
    exact ⟨.inr d, rfl, hd⟩
  obtain ⟨runs, hr, hri, hrl⟩ := disjoint_cycles_remove_edges_bound sr dt Sum.isLeft Z
    cycles hc hd hall hmark
  have henum := hi.trans (sum_univ_list_perm (E := E) (D := D))
  have hcount : cycles.flatten.countP (fun e => !e.isLeft) = Fintype.card D := by
    have h := henum.countP_eq (fun e => !e.isLeft)
    simpa [Function.comp_def] using h
  have hinv : runs.flatten.Perm ((Finset.univ.toList : List E).map Sum.inl) := by
    have h := hri.trans (henum.filter Sum.isLeft)
    simpa [List.filter_map, Function.comp_def] using h
  have hleft : ∀ es ∈ runs, ∀ e ∈ es, e.isLeft = true := by
    intro es hes e he
    have hm := hinv.mem_iff.mp (List.mem_flatten.mpr ⟨es, hes, he⟩)
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm
    rfl
  let trails := runs.map (List.filterMap Sum.getLeft?)
  have hpaths : DirectedTrails src dst trails := by
    intro es hes
    obtain ⟨rs, hrs, rfl⟩ := List.mem_map.mp hes
    obtain ⟨hne, a, b, hp⟩ := hr rs hrs
    obtain ⟨hm, hmi⟩ := hp.left_labels (hleft rs hrs)
    refine ⟨?_, a, b, hm⟩
    intro hz
    rw [hz] at hmi
    exact hne hmi.symm
  have hperm : trails.flatten.Perm Finset.univ.toList := by
    have h := hinv.filterMap Sum.getLeft?
    simpa [trails, List.filterMap_flatten, List.filterMap_map] using h
  refine ⟨trails, hpaths, hperm, Nat.le_min.mpr ⟨?_, ?_⟩⟩
  · have h := hpaths.length_le_flatten
    rw [hperm.length_eq] at h
    simpa using h
  · have hslots := balancingDummy_card_le_nonzeroVertices src dst hb
    have hzero : (nonzeroVertices src dst).card + Z.card = Fintype.card V := by
      have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun v => degreeImbalance src dst v ≠ 0)
      simpa only [nonzeroVertices, not_not, Z, Finset.card_univ] using h
    have hlen : trails.length = runs.length := List.length_map _
    rw [hcount] at hrl
    change Fintype.card D ≤ _ at hslots
    omega

end SuperpermutationUpperBound
