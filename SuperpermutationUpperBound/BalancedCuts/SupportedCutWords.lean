import SuperpermutationUpperBound.BalancedCuts.CutWords
import SuperpermutationUpperBound.Assembly.SupportedStates

namespace SuperpermutationUpperBound.BalancedCuts
variable {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α] {h ell : Nat}

/-- A concrete state-alphabet form of the balanced-cut word theorem. The
state count is derived from literal injective endpoint lists. -/
theorem balanced_supported_cut_words (words : I × Fin h → List α) (lengths : I → Nat)
    (A : Finset α) (hh : 0 < h) (hl : ∀ c, (words c).length = lengths c.1)
    (hell : ∀ i, ell ≤ lengths i)
    (hp : ∀ c, ((words c).take ell).Nodup ∧ ∀ a ∈ (words c).take ell, a ∈ A)
    (ht : ∀ c, ((words c).drop ((words c).length - ell)).Nodup ∧
      ∀ a ∈ (words c).drop ((words c).length - ell), a ∈ A)
    (hbalance : ∀ i,
      ((List.finRange h).map (fun j => (words (i,j)).take ell)).Perm
        ((List.finRange h).map (fun j => (words (i,j)).drop ((words (i,j)).length - ell))))
    (P : α → Prop) (hsupport : ∀ c, ∀ a ∈ words c, P a) :
    ∃ selected : I → Fin h, ∃ J : Nat, ∃ w : List α,
      J ≤ min (Fintype.card I) (A.card.descFactorial ell) ∧
      w.length = (∑ i, lengths i) - ell * (Fintype.card I - J) ∧
      (∀ i, (words (i, selected i)).IsInfix w) ∧ ∀ a ∈ w, P a := by
  classical
  let source : I × Fin h → supportedOverlapState A ell := fun c =>
    ⟨(words c).take ell, by rw [List.length_take, hl]; exact Nat.min_eq_left (hell c.1), hp c⟩
  let target : I × Fin h → supportedOverlapState A ell := fun c =>
    ⟨(words c).drop ((words c).length - ell), by
      rw [List.length_drop, Nat.sub_sub_self (by rw [hl]; exact hell c.1)], ht c⟩
  have hbal : ∀ i, ((List.finRange h).map (fun j => source (i,j))).Perm
      ((List.finRange h).map (fun j => target (i,j))) := by
    intro i
    apply (List.map_perm_map_iff (f := fun v : supportedOverlapState A ell => v.val)
      Subtype.val_injective).mp
    simpa [List.map_map, Function.comp_def, source, target] using hbalance i
  obtain ⟨selected, J, w, hJ, hw, hc, hs⟩ := balanced_cut_words words lengths source target
    Subtype.val hh hl hell (fun _ => rfl) (fun _ => rfl) hbal P hsupport
  exact ⟨selected, J, w, by simpa only [supportedOverlapState_card] using hJ, hw, hc, hs⟩

end SuperpermutationUpperBound.BalancedCuts
