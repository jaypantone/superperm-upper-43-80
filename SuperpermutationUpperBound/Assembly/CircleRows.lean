import SuperpermutationUpperBound.Assembly.RowMacroFamily
import SuperpermutationUpperBound.Assembly.ConnectorWords
import SuperpermutationUpperBound.Foundation.SupportedWords

namespace SuperpermutationUpperBound
variable {I : Type} [Fintype I] {K ell : Nat}

/-- Actual closed row trails with a literal circle cover give a finite-alphabet
superpermutation and an exact natural ledger. -/
theorem exists_word_of_circle_rows (rows : I → List (Row Nat)) (circles : List (List Nat))
    (hK : 4 ≤ K) (hell : ell ≤ K - 3)
    (hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = K)
    (hv : ∀ i r, r ∈ rows i → 1 ≤ r.visible)
    (hclosed : ∀ i, ClosedTrail (rows i))
    (hc : CircleTransport.CircleFamilyValid (K - 3) circles)
    (hcover : CircleTransport.CoversDesignated circles (fun i => CircleTransport.HeadVertex (rows i)))
    (A : Finset Nat) (hA : ∀ c ∈ circles, ∀ a ∈ c, a ∈ A)
    (hcs : ∀ c ∈ circles, ∀ a ∈ c, a < K)
    (hs : ∀ i r, r ∈ rows i → ∀ a ∈ r.word, a < K)
    (hperms : ∀ p : List Nat, p.Perm (List.range K) → ∃ i, ∃ r ∈ rows i, r.Assigned p) :
    ∃ t J : Nat, ∃ w : Word K, IsSuperpermutation w ∧
      t ≤ circles.length ∧ J ≤ min t (A.card.descFactorial ell) ∧
      w.length = (K + 1) *
        (((Finset.univ.toList : List I).flatMap rows).map Row.visible).sum +
        ((Finset.univ.toList : List I).flatMap rows).length + (K - 3) * circles.length +
        (K - 4) * t - ell * (t - J) := by
  classical
  let edges := RowMacroFamily.edges rows hlen
  let circle : Fin circles.length → List Nat := fun c => circles[c.val]
  have hclen : ∀ c, (circle c).length = K - 3 := fun c => (hc _ (List.getElem_mem c.isLt)).1
  obtain ⟨t, J, w, ht, hJ, hw, hrows, hsupport⟩ := ConnectorFamily.exists_word
    edges circle hclen (by omega) hell (RowMacroFamily.edges_closed rows hlen hK hclosed hv)
    (RowMacroFamily.edges_cover rows hlen circles hc hcover) A
    (fun c => (hc _ (List.getElem_mem c.isLt)).2)
    (fun c => hA _ (List.getElem_mem c.isLt)) (fun a => a < K)
    (RowMacroFamily.edges_support rows hlen _ hs)
    (fun c => hcs _ (List.getElem_mem c.isLt))
  have hcost : (∑ i, ((edges i).map MacroEdge.cost).sum) =
      (K + 1) * (((Finset.univ.toList : List I).flatMap rows).map Row.visible).sum +
        ((Finset.univ.toList : List I).flatMap rows).length := by
    simp_rw [show ∀ i, ((edges i).map MacroEdge.cost).sum =
      (K + 1) * ((rows i).map Row.visible).sum + (rows i).length from
        RowMacroFamily.edges_cost rows hlen hK hv]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, finite_family_cost_sum, finite_family_length_sum]
  have hperm : CoversPermutationsOf (List.range K) w := by
    intro p hp
    obtain ⟨i, r, hr, ha⟩ := hperms p hp
    obtain ⟨edge, he, hword⟩ := RowMacroFamily.edges_word_mem rows hlen i r hr
    exact (r.assigned_infix_word ha).trans (hword ▸ hrows i edge he)
  refine ⟨t, J, liftWord w hsupport, isSuperpermutation_liftWord_of_covers w hsupport hperm,
    by simpa using ht, hJ, ?_⟩
  rw [liftWord_length]
  rw [hcost, Fintype.card_fin] at hw
  simpa only [show K - 3 - 1 = K - 4 by omega] using hw

end SuperpermutationUpperBound
