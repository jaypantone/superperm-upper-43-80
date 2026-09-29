import SuperpermutationUpperBound.Assembly.OccurrencePaths
import SuperpermutationUpperBound.Assembly.RotationEdges
import SuperpermutationUpperBound.Assembly.ModuleCosts

namespace SuperpermutationUpperBound.ConnectorFamily
variable {I C α : Type} {h : Nat}

/-- Row trails and ordinary connector circles form one family. Positions
inside every member remain separate occurrence labels. -/
def family (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) : I ⊕ C → List (MacroEdge α h) :=
  Sum.elim rows (fun c => rotationMacroCycle (circle c) (hlen c) hh)

abbrev Label (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) :=
  FamilyOccurrence (family rows circle hlen hh)

def payload (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) : Label rows circle hlen hh → MacroEdge α h :=
  familyOccurrenceValue (family rows circle hlen hh)

def circleLabel (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (c : C) (j : Nat) (hj : j < h) :
    Label rows circle hlen hh :=
  ⟨.inr c, ⟨j, by simpa only [family, Sum.elim_inr, rotationMacroCycle_length] using hj⟩⟩

@[simp] theorem circleLabel_payload (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (c : C) (j : Nat) (hj : j < h) :
    payload rows circle hlen hh (circleLabel rows circle hlen hh c j hj) =
      rotationMacro (circle c) (hlen c) hh j := by
  simp only [payload, circleLabel, familyOccurrenceValue, family, Sum.elim_inr,
    rotationMacroCycle_get]

def cycle (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (i : I ⊕ C) :
    List (Label rows circle hlen hh) := familyOccurrenceCycle (family rows circle hlen hh) i

@[simp] theorem label_mem_own_cycle (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (e : Label rows circle hlen hh) :
    e ∈ cycle rows circle hlen hh e.1 := by
  exact List.mem_map.mpr ⟨e.2, List.mem_finRange _, by cases e; rfl⟩

theorem cycles_closed (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h)
    (hr : ∀ i, rows i ≠ [] ∧ ∃ v, EdgePath MacroEdge.source MacroEdge.target v (rows i) v) :
    ∀ i, (cycle rows circle hlen hh i) ≠ [] ∧
      ∃ v, EdgePath (fun e => (payload rows circle hlen hh e).source)
        (fun e => (payload rows circle hlen hh e).target) v (cycle rows circle hlen hh i) v := by
  intro i
  have hn : family rows circle hlen hh i ≠ [] := by
    cases i with
    | inl i => exact (hr i).1
    | inr c =>
      intro hz
      change rotationMacroCycle (circle c) (hlen c) hh = [] at hz
      have hl := rotationMacroCycle_length (circle c) (hlen c) hh
      rw [hz] at hl
      simp at hl
      omega
  constructor
  · intro he
    have hl := congrArg List.length he
    simp only [cycle, familyOccurrenceCycle, List.length_map, List.length_finRange,
      List.length_nil] at hl
    exact hn (List.length_eq_zero_iff.mp hl)
  · have hp : ∃ v, EdgePath MacroEdge.source MacroEdge.target v (family rows circle hlen hh i) v := by
      cases i with
      | inl i => exact (hr i).2
      | inr c => exact ⟨circle c, rotationMacroCycle_closed (circle c) (hlen c) hh⟩
    obtain ⟨v, hv⟩ := hp
    exact ⟨v, familyOccurrenceCycle_path (family rows circle hlen hh) i hv⟩

theorem cycles_inventory [Fintype I] [Fintype C]
    (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) :
    ((Finset.univ.toList : List (I ⊕ C)).flatMap (cycle rows circle hlen hh)).Perm
      Finset.univ.toList := familyOccurrence_inventory ..

/-- Any two ordinary edges of a selected rotation circle are connected in
the combined labelled graph. -/
theorem circle_connected (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (c : C)
    (j k : Nat) (hj : j < h) (hk : k < h) :
    EdgeConnected (fun e => (payload rows circle hlen hh e).source)
      (fun e => (payload rows circle hlen hh e).target)
      (circleLabel rows circle hlen hh c j hj) (circleLabel rows circle hlen hh c k hk) := by
  have hp := familyOccurrenceCycle_path (family rows circle hlen hh) (.inr c)
    (rotationMacroCycle_closed (circle c) (hlen c) hh)
  exact hp.connected_edges (label_mem_own_cycle ..) (label_mem_own_cycle ..)

def rowLabel (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (i : I)
    (j : Fin (rows i).length) : Label rows circle hlen hh := ⟨.inl i, j⟩

@[simp] theorem rowLabel_payload (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (i : I)
    (j : Fin (rows i).length) :
    payload rows circle hlen hh (rowLabel rows circle hlen hh i j) = (rows i)[j.val] := rfl

/-- A row trail meeting a connector at an actual source vertex connects
every occurrence in that trail to the connector's distinguished edge. -/
theorem cover_connected (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h)
    (hr : ∀ i, rows i ≠ [] ∧ ∃ v, EdgePath MacroEdge.source MacroEdge.target v (rows i) v)
    (hcover : ∀ i, ∃ c, ∃ edge ∈ rows i, ∃ j, j < h ∧ edge.source = rot (circle c) j) :
    ∀ e, ∃ c, EdgeConnected (fun e => (payload rows circle hlen hh e).source)
      (fun e => (payload rows circle hlen hh e).target)
      e (circleLabel rows circle hlen hh c 0 hh) := by
  rintro ⟨tag, pos⟩
  cases tag with
  | inr c =>
    exact ⟨c, circle_connected rows circle hlen hh c pos.val 0
      (by simpa only [family, Sum.elim_inr, rotationMacroCycle_length] using pos.isLt) hh⟩
  | inl i =>
    obtain ⟨c, edge, he, j, hj, hs⟩ := hcover i
    obtain ⟨k, hk, hek⟩ := List.mem_iff_getElem.mp he
    let f := rowLabel rows circle hlen hh i ⟨k, hk⟩
    have hf : (payload rows circle hlen hh f).source = rot (circle c) j := by
      change (rows i)[k].source = _
      rw [hek]
      exact hs
    obtain ⟨v, hv⟩ := (cycles_closed rows circle hlen hh hr (.inl i)).2
    have hef := hv.connected_edges
      (label_mem_own_cycle rows circle hlen hh ⟨.inl i, pos⟩)
      (label_mem_own_cycle rows circle hlen hh f)
    have hfg : EdgeConnected (fun e => (payload rows circle hlen hh e).source)
        (fun e => (payload rows circle hlen hh e).target)
        f (circleLabel rows circle hlen hh c j hj) := by
      apply EdgeConnected.link
      exact ⟨rot (circle c) j, Or.inl hf, Or.inl (by simp)⟩
    exact ⟨c, hef.trans (hfg.trans (circle_connected rows circle hlen hh c j 0 hj hh))⟩

/-- Arbitrary natural cut indices are reduced to the valid rotation range. -/
def cut (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (c : C) (j : Nat) :
    Label rows circle hlen hh := circleLabel rows circle hlen hh c (j % h) (Nat.mod_lt _ hh)

@[simp] theorem cut_eq (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (c : C) (j : Nat) (hj : j < h) :
    cut rows circle hlen hh c j = circleLabel rows circle hlen hh c j hj := by
  simp only [cut, Nat.mod_eq_of_lt hj]

def Required {rows : I → List (MacroEdge α h)} {circle : C → List α}
    {hlen : ∀ c, (circle c).length = h} {hh : 0 < h} (e : Label rows circle hlen hh) : Prop :=
  e.1.isLeft

theorem required_ne_cut (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h)
    (e : Label rows circle hlen hh) (he : Required e) (c : C) (j : Nat) :
    e ≠ cut rows circle hlen hh c j := by
  intro hz
  subst e
  simp [Required, cut, circleLabel] at he

theorem payload_support (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (P : α → Prop)
    (hr : ∀ i edge, edge ∈ rows i → ∀ a ∈ edge.word, P a)
    (hc : ∀ c, ∀ a ∈ circle c, P a) :
    ∀ e, ∀ a ∈ (payload rows circle hlen hh e).word, P a := by
  rintro ⟨tag, pos⟩ a ha
  cases tag with
  | inl i => exact hr i _ (List.getElem_mem pos.isLt) a ha
  | inr c =>
    exact hc c a (rotationMacroCycle_support (circle c) (hlen c) hh
      _ (List.getElem_mem pos.isLt) a ha)

theorem payload_cost_sum [Fintype I] [Fintype C]
    (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) :
    (∑ e, (payload rows circle hlen hh e).cost) =
      (∑ i, ((rows i).map MacroEdge.cost).sum) + h * Fintype.card C := by
  rw [Fintype.sum_sigma]
  change (∑ tag : I ⊕ C, ∑ pos : Fin (family rows circle hlen hh tag).length,
    ((family rows circle hlen hh tag)[pos.val]).cost) = _
  simp_rw [list_index_sum]
  rw [Fintype.sum_sum_type]
  have hc : ∀ c, ((rotationMacroCycle (circle c) (hlen c) hh).map MacroEdge.cost).sum = h := by
    intro c
    simp [rotationMacroCycle, List.map_map, Function.comp_def]
  simp only [family, Sum.elim_inl, Sum.elim_inr, hc]
  simp [Nat.mul_comm]

theorem payload_cost_list_sum [Fintype I] [Fintype C]
    (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) :
    ((Finset.univ.toList : List (Label rows circle hlen hh)).map
      (fun e => (payload rows circle hlen hh e).cost)).sum =
      (∑ i, ((rows i).map MacroEdge.cost).sum) + h * Fintype.card C := by
  classical
  rw [← List.sum_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset]
  exact payload_cost_sum ..

end SuperpermutationUpperBound.ConnectorFamily
