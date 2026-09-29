import SuperpermutationUpperBound.BalancedCuts.SelectedGraph
import SuperpermutationUpperBound.Assembly.GraphTrails
import SuperpermutationUpperBound.Assembly.WordTrails

namespace SuperpermutationUpperBound.BalancedCuts
namespace ChoiceSystem

variable {I V C α : Type} [Fintype I] [Fintype V] [Fintype C]
  [DecidableEq I] [DecidableEq V] {h : Nat}

/-- Sharp rounding followed by labelled graph assembly gives an actual word.
The finite states need only map to the literal endpoint words; the state map
need not be injective. Costs are constant across candidates for each item. -/
theorem Feasible.exists_word_assembly {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.Feasible x) (payload : C → MacroEdge α h) (vertexWord : V → List α)
    (hsrc : ∀ c, (payload c).source = vertexWord (S.source c))
    (hdst : ∀ c, (payload c).target = vertexWord (S.target c))
    (itemCost : I → Nat) (hcost : ∀ c, (payload c).cost = itemCost (S.item c))
    (P : α → Prop) (hs : ∀ c, 0 < x c → ∀ a ∈ (payload c).word, P a) :
    ∃ choice : I → C, ∃ J : Nat, ∃ w : List α,
      (∀ i, S.item (choice i) = i ∧ 0 < x (choice i)) ∧
      J ≤ min (Fintype.card I) (Fintype.card V) ∧
      w.length = (∑ i, itemCost i) + h * J ∧
      (∀ i, (payload (choice i)).word.IsInfix w) ∧ ∀ a ∈ w, P a := by
  classical
  obtain ⟨y, hyint, hym, hypos, hycard, _hyunique, hybound⟩ := hx.exists_selected_graph
  obtain ⟨trails, ht, hi, hj⟩ := directed_graph_trail_bound
    (S.selectedSource y) (S.selectedTarget y) hybound
  let pl : Selected y → MacroEdge α h := fun c => payload c
  have hpaths : DirectedTrails (fun c => (pl c).source) (fun c => (pl c).target) trails := by
    intro es hes
    obtain ⟨hne, a, b, hp⟩ := ht es hes
    refine ⟨hne, vertexWord a, vertexWord b, ?_⟩
    have hm := hp.map_vertices vertexWord
    simpa only [selectedSource, selectedTarget, ← hsrc, ← hdst, pl] using hm
  obtain ⟨w, hwlen, hcover, hsupport⟩ := exists_word_of_directed_trails pl trails
    hpaths hi P (fun c => hs c (hypos c))
  let eqv := S.integralSupportEquiv y hym hyint
  let choice : I → C := fun i => (eqv.symm i).val
  have hchoice : ∀ i, S.item (choice i) = i := by
    intro i
    exact eqv.apply_symm_apply i
  have hsum : (∑ c : Selected y, (pl c).cost) = ∑ i, itemCost i := by
    calc
      _ = ∑ c : Selected y, itemCost (S.item c) :=
        Finset.sum_congr rfl (fun c _ => hcost c)
      _ = ∑ c : Selected y, itemCost (eqv c) := rfl
      _ = _ := eqv.sum_comp itemCost
  refine ⟨choice, trails.length, w, fun i => ⟨hchoice i, hypos (eqv.symm i)⟩,
    ?_, ?_, fun i => hcover (eqv.symm i), hsupport⟩
  · simpa only [hycard] using hj
  · exact hwlen.trans (congrArg (fun n => n + h * trails.length) hsum)

/-- Every candidate for an item may carry all factors assigned to that item.
The chosen word then contains every assigned factor, regardless of which
supported candidate is selected by rounding. -/
theorem Feasible.exists_word_covering {S : ChoiceSystem I V C} {x : C → ℚ}
    (hx : S.Feasible x) (payload : C → MacroEdge α h) (vertexWord : V → List α)
    (hsrc : ∀ c, (payload c).source = vertexWord (S.source c))
    (hdst : ∀ c, (payload c).target = vertexWord (S.target c))
    (itemCost : I → Nat) (hcost : ∀ c, (payload c).cost = itemCost (S.item c))
    (Assigned : I → List α → Prop)
    (ha : ∀ c, 0 < x c → ∀ p, Assigned (S.item c) p → p.IsInfix (payload c).word)
    (P : α → Prop) (hs : ∀ c, 0 < x c → ∀ a ∈ (payload c).word, P a) :
    ∃ J : Nat, ∃ w : List α, J ≤ min (Fintype.card I) (Fintype.card V) ∧
      w.length = (∑ i, itemCost i) + h * J ∧
      (∀ i p, Assigned i p → p.IsInfix w) ∧ ∀ a ∈ w, P a := by
  obtain ⟨choice, J, w, hc, hj, hl, hw, hp⟩ :=
    hx.exists_word_assembly payload vertexWord hsrc hdst itemCost hcost P hs
  refine ⟨J, w, hj, hl, ?_, hp⟩
  intro i p hip
  have hi : Assigned (S.item (choice i)) p := (hc i).1.symm ▸ hip
  exact (ha (choice i) (hc i).2 p hi).trans (hw i)

/-- Equal candidate lengths per item give the natural-subtraction word
ledger. Its subtraction is justified by the additive-cleared equality in
the proof and the bound `J ≤ card I`. -/
theorem Feasible.exists_word_assembly_of_lengths
    {S : ChoiceSystem I V C} {x : C → ℚ} (hx : S.Feasible x)
    (payload : C → MacroEdge α h) (vertexWord : V → List α)
    (hsrc : ∀ c, (payload c).source = vertexWord (S.source c))
    (hdst : ∀ c, (payload c).target = vertexWord (S.target c))
    (itemLength : I → Nat)
    (hlen : ∀ c, (payload c).word.length = itemLength (S.item c))
    (P : α → Prop) (hs : ∀ c, 0 < x c → ∀ a ∈ (payload c).word, P a) :
    ∃ choice : I → C, ∃ J : Nat, ∃ w : List α,
      (∀ i, S.item (choice i) = i ∧ 0 < x (choice i)) ∧
      J ≤ min (Fintype.card I) (Fintype.card V) ∧
      w.length = (∑ i, itemLength i) - h * (Fintype.card I - J) ∧
      (∀ i, (payload (choice i)).word.IsInfix w) ∧ ∀ a ∈ w, P a := by
  have hcost : ∀ c, (payload c).cost = itemLength (S.item c) - h := by
    intro c
    rw [MacroEdge.cost, hlen]
  obtain ⟨choice, J, w, hc, hj, hl, hw, hp⟩ :=
    hx.exists_word_assembly payload vertexWord hsrc hdst
      (fun i => itemLength i - h) hcost P hs
  have hmin : ∀ i, h ≤ itemLength i := by
    intro i
    have hi := (payload (choice i)).length_ge
    rwa [hlen, (hc i).1] at hi
  have hsum : (∑ i, (itemLength i - h)) + h * Fintype.card I = ∑ i, itemLength i := by
    calc
      _ = ∑ i, ((itemLength i - h) + h) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          smul_eq_mul, Nat.mul_comm]
      _ = _ := Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hmin i))
  have hJi : J ≤ Fintype.card I := (Nat.le_min.mp hj).1
  have hclear : w.length + h * (Fintype.card I - J) = ∑ i, itemLength i := by
    rw [hl, Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_of_le hJi]
    exact hsum
  refine ⟨choice, J, w, hc, hj, ?_, hw, hp⟩
  omega

end ChoiceSystem
end SuperpermutationUpperBound.BalancedCuts
