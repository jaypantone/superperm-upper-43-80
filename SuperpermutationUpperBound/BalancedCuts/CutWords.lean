import SuperpermutationUpperBound.BalancedCuts.UniformChoices
import SuperpermutationUpperBound.BalancedCuts.WordAssembly

namespace SuperpermutationUpperBound.BalancedCuts
variable {I V α : Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {h ell : Nat}

/-- Equal-length cut choices with balanced endpoint distributions yield a
literal word with the sharp overlap cost. A finite state may name any
literal endpoint word, so equal endpoint values need not have unique labels. -/
theorem balanced_cut_words (words : I × Fin h → List α) (lengths : I → Nat)
    (source target : I × Fin h → V) (vertexWord : V → List α)
    (hh : 0 < h) (hl : ∀ c, (words c).length = lengths c.1)
    (hell : ∀ i, ell ≤ lengths i)
    (hs : ∀ c, (words c).take ell = vertexWord (source c))
    (ht : ∀ c, (words c).drop ((words c).length - ell) = vertexWord (target c))
    (hbalance : ∀ i, ((List.finRange h).map (fun j => source (i,j))).Perm
      ((List.finRange h).map (fun j => target (i,j))))
    (P : α → Prop) (hsupport : ∀ c, ∀ a ∈ words c, P a) :
    ∃ selected : I → Fin h, ∃ J : Nat, ∃ w : List α,
      J ≤ min (Fintype.card I) (Fintype.card V) ∧
      w.length = (∑ i, lengths i) - ell * (Fintype.card I - J) ∧
      (∀ i, (words (i, selected i)).IsInfix w) ∧ ∀ a ∈ w, P a := by
  classical
  let S := uniformSystem source target
  let payload : I × Fin h → MacroEdge α ell :=
    fun c => ⟨words c, by rw [hl]; exact hell c.1⟩
  have hfeas := uniform_feasible source target hh hbalance
  obtain ⟨choice, J, w, hchoice, hJ, hlen, hcover, hw⟩ :=
    hfeas.exists_word_assembly_of_lengths payload vertexWord hs ht lengths hl P
      (fun c _ => hsupport c)
  refine ⟨fun i => (choice i).2, J, w, hJ, hlen, ?_, hw⟩
  intro i
  have hi : (choice i).1 = i := (hchoice i).1
  have hc := hcover i
  change (words (choice i)).IsInfix w at hc
  rw [show (i, (choice i).2) = choice i from Prod.ext hi.symm rfl]
  exact hc

end SuperpermutationUpperBound.BalancedCuts
