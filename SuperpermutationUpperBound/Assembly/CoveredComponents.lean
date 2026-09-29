import SuperpermutationUpperBound.Assembly.CycleTrailCount

namespace SuperpermutationUpperBound
variable {E V C : Type}

/-- Connectivity of edge labels through shared endpoint values. -/
inductive EdgeConnected (src dst : E → V) : E → E → Prop
  | refl (e : E) : EdgeConnected src dst e e
  | link {e f : E} (hv : ∃ v, (src e = v ∨ dst e = v) ∧ (src f = v ∨ dst f = v)) :
      EdgeConnected src dst e f
  | trans {e f g : E} : EdgeConnected src dst e f → EdgeConnected src dst f g →
      EdgeConnected src dst e g

namespace EdgeConnected
variable {src dst : E → V}

theorem symm {e f : E} (h : EdgeConnected src dst e f) : EdgeConnected src dst f e := by
  induction h with
  | refl e => exact .refl e
  | link hv =>
    obtain ⟨v, he, hf⟩ := hv
    exact .link ⟨v, hf, he⟩
  | trans _ _ ih1 ih2 => exact ih2.trans ih1

/-- A complete, vertex-disjoint cycle decomposition cannot separate
connected edge labels. -/
theorem same_cycle {cycles : List (List E)}
    (hd : cycles.Pairwise (DisjointIncidence src dst))
    (hall : ∀ e, ∃ es ∈ cycles, e ∈ es)
    {es : List E} (hes : es ∈ cycles) {e f : E}
    (h : EdgeConnected src dst e f) (he : e ∈ es) : f ∈ es := by
  induction h with
  | refl => exact he
  | @link e f hv =>
    obtain ⟨v, hev, hfv⟩ := hv
    obtain ⟨other, ho, hf⟩ := hall f
    have heq := disjoint_cycles_common_vertex hd hes ho ⟨e, he, hev⟩ ⟨f, hf, hfv⟩
    exact heq ▸ hf
  | trans _ _ ih1 ih2 => exact ih2 (ih1 he)

end EdgeConnected

/-- All edge labels of one directed path are connected. -/
theorem EdgePath.connected_edges {src dst : E → V} {a b : V} {es : List E}
    (hp : EdgePath src dst a es b) {e f : E} (he : e ∈ es) (hf : f ∈ es) :
    EdgeConnected src dst e f := by
  induction hp generalizing e f with
  | nil => simp at he
  | @cons a b x xs hx ht ih =>
    have hhead : ∀ g ∈ xs, EdgeConnected src dst x g := by
      intro g hg
      cases xs with
      | nil => simp at hg
      | cons y ys =>
        have hy := ht.source_eq_of_cons
        have hxy : EdgeConnected src dst x y := .link ⟨dst x, Or.inr rfl, Or.inl hy⟩
        exact hxy.trans (ih (by simp) hg)
    rcases List.mem_cons.mp he with hex | hem
    · subst e
      rcases List.mem_cons.mp hf with hfx | hfm
      · subst f
        exact .refl _
      · exact hhead f hfm
    · rcases List.mem_cons.mp hf with hfx | hfm
      · subst f
        exact (hhead e hem).symm
      · exact ih hem hfm


/-- If each vertex-disjoint cycle contains a distinguished edge of some
finite label, their number is bounded by the number of those labels. -/
theorem disjoint_cycles_length_le_markers [Fintype C]
    (src dst : E → V) (cycles : List (List E)) (marker : C → E)
    (hd : cycles.Pairwise (DisjointIncidence src dst))
    (hc : ∀ es ∈ cycles, ∃ c, marker c ∈ es) : cycles.length ≤ Fintype.card C := by
  classical
  have hchoice : ∀ i : Fin cycles.length, ∃ c, marker c ∈ cycles[i.val] :=
    fun i => hc _ (List.getElem_mem i.isLt)
  choose label hl using hchoice
  have hinj : Function.Injective label := by
    intro i j hij
    by_contra hne
    have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hlt : i.val < j.val ∨ j.val < i.val := by omega
    have hi : EdgeIncident src dst cycles[i.val] (src (marker (label i))) :=
      ⟨marker (label i), hl i, Or.inl rfl⟩
    have hj : EdgeIncident src dst cycles[j.val] (src (marker (label i))) :=
      ⟨marker (label j), hl j, Or.inl (congrArg (fun c => src (marker c)) hij.symm)⟩
    rcases hlt with hlt | hlt
    · exact (List.pairwise_iff_getElem.mp hd _ _ i.isLt j.isLt hlt) _ ⟨hi, hj⟩
    · exact (List.pairwise_iff_getElem.mp hd _ _ j.isLt i.isLt hlt) _ ⟨hj, hi⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective label hinj

/-- Closed cycle families covered by `card C` distinguished connector edges
splice into at most `card C` modules. Repeated actual endpoint values cause
no difficulty; the proof retains the complete labelled edge inventory. -/
theorem covered_closed_components [Fintype E] [Fintype C]
    (src dst : E → V) (cycles : List (List E)) (marker : C → E)
    (hc : ClosedCycles src dst cycles) (hi : cycles.flatten.Perm Finset.univ.toList)
    (hcover : ∀ e, ∃ c, EdgeConnected src dst e (marker c)) :
    ∃ modules, ClosedCycles src dst modules ∧ modules.flatten.Perm Finset.univ.toList ∧
      modules.Pairwise (DisjointIncidence src dst) ∧
      (∀ es ∈ modules, ∃ c, marker c ∈ es) ∧ modules.length ≤ Fintype.card C := by
  obtain ⟨modules, hm, hp, hd⟩ := closed_cycles_disjoint_decomposition src dst cycles hc
  have hinv := hp.trans hi
  have hall : ∀ e, ∃ es ∈ modules, e ∈ es :=
    fun e => List.mem_flatten.mp (hinv.mem_iff.mpr (by simp))
  have hmarkers : ∀ es ∈ modules, ∃ c, marker c ∈ es := by
    intro es hes
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil es (hm es hes).1
    obtain ⟨c, hc⟩ := hcover e
    exact ⟨c, hc.same_cycle hd hall hes he⟩
  exact ⟨modules, hm, hinv, hd, hmarkers,
    disjoint_cycles_length_le_markers src dst modules marker hd hmarkers⟩

end SuperpermutationUpperBound
