import SuperpermutationUpperBound.Assembly.ConnectorFamily
import SuperpermutationUpperBound.Assembly.BalancedCircleWords

namespace SuperpermutationUpperBound.ConnectorFamily
variable {I C α : Type} [Fintype I] [Fintype C] [DecidableEq α] {h ell : Nat}

/-- Closed row-edge trails covered by selected rotation circles give a
single literal word with the exact connector and short-overlap ledger. -/
theorem exists_word (rows : I → List (MacroEdge α h)) (circle : C → List α)
    (hlen : ∀ c, (circle c).length = h) (hh : 0 < h) (hell : ell ≤ h)
    (hr : ∀ i, rows i ≠ [] ∧ ∃ v, EdgePath MacroEdge.source MacroEdge.target v (rows i) v)
    (hcover : ∀ i, ∃ c, ∃ edge ∈ rows i, ∃ j, j < h ∧ edge.source = rot (circle c) j)
    (A : Finset α) (hnd : ∀ c, (circle c).Nodup)
    (hA : ∀ c, ∀ a ∈ circle c, a ∈ A) (P : α → Prop)
    (hrows : ∀ i edge, edge ∈ rows i → ∀ a ∈ edge.word, P a)
    (hcircles : ∀ c, ∀ a ∈ circle c, P a) :
    ∃ t J : Nat, ∃ w : List α,
      t ≤ Fintype.card C ∧ J ≤ min t (A.card.descFactorial ell) ∧
      w.length = (∑ i, ((rows i).map MacroEdge.cost).sum) + h * Fintype.card C +
        (h - 1) * t - ell * (t - J) ∧
      (∀ i edge, edge ∈ rows i → edge.word.IsInfix w) ∧ ∀ a ∈ w, P a := by
  classical
  let cycles := (Finset.univ.toList : List (I ⊕ C)).map (cycle rows circle hlen hh)
  have hc : ClosedCycles (fun e => (payload rows circle hlen hh e).source)
      (fun e => (payload rows circle hlen hh e).target) cycles := by
    intro es hes
    obtain ⟨tag, _, rfl⟩ := List.mem_map.mp hes
    exact cycles_closed rows circle hlen hh hr tag
  have hi : cycles.flatten.Perm Finset.univ.toList := by
    simpa only [cycles, List.flatMap_def] using cycles_inventory rows circle hlen hh
  have hcut : ∀ c j, j < h → (payload rows circle hlen hh (cut rows circle hlen hh c j)).cost = 1 ∧
      (payload rows circle hlen hh (cut rows circle hlen hh c j)).source = rot (circle c) j ∧
      (payload rows circle hlen hh (cut rows circle hlen hh c j)).target = rot (circle c) (j + 1) := by
    intro c j hj
    simp [cut_eq _ _ _ _ _ _ hj]
  have hconn : ∀ c j, j < h → EdgeConnected
      (fun e => (payload rows circle hlen hh e).source)
      (fun e => (payload rows circle hlen hh e).target)
      (cut rows circle hlen hh c 0) (cut rows circle hlen hh c j) := by
    intro c j hj
    rw [cut_eq _ _ _ _ _ _ hh, cut_eq _ _ _ _ _ _ hj]
    exact circle_connected rows circle hlen hh c 0 j hh hj
  have hcov : ∀ e, ∃ c, EdgeConnected (fun e => (payload rows circle hlen hh e).source)
      (fun e => (payload rows circle hlen hh e).target) e (cut rows circle hlen hh c 0) := by
    intro e
    simpa only [cut_eq _ _ _ _ _ _ hh] using cover_connected rows circle hlen hh hr hcover e
  obtain ⟨modules, J, w, _, hmod, hJ, hw, hkeep, hs⟩ :=
    balanced_covered_circle_words (payload rows circle hlen hh) cycles circle
      (cut rows circle hlen hh) Required P A hh hell hc hi hlen hnd hA hcut hconn hcov
      (fun e he c j _ => required_ne_cut rows circle hlen hh e he c j)
      (payload_support rows circle hlen hh P hrows hcircles)
  refine ⟨modules.length, J, w, hmod, hJ, ?_, ?_, hs⟩
  · rw [payload_cost_list_sum] at hw
    exact hw
  · intro i edge he
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp he
    have hhkeep := hkeep (rowLabel rows circle hlen hh i ⟨j,hj⟩) (by simp [Required, rowLabel])
    simpa only [rowLabel_payload, hje] using hhkeep

end SuperpermutationUpperBound.ConnectorFamily
