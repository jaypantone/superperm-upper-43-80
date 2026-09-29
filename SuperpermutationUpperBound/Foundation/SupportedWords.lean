import SuperpermutationUpperBound.Foundation.Relabeling

/-! Convert a natural-letter word supported below K into an actual Word K.
Only letters occurring in the word are lifted; no bijection Nat ≃ Fin K is used. -/
namespace SuperpermutationUpperBound

/-- Lift every occurrence using its supplied alphabet-bound proof. -/
def liftWord {K : Nat} (w : List Nat) (bound : ∀ a ∈ w, a < K) : Word K :=
  w.attach.map (fun a => ⟨a.val, bound a.val a.property⟩)

@[simp] theorem liftWord_map_val {K : Nat} (w : List Nat) (bound : ∀ a ∈ w, a < K) :
    (liftWord w bound).map Fin.val = w := by
  simp only [liftWord, List.map_map]
  exact List.attach_map_subtype_val w

@[simp] theorem liftWord_length {K : Nat} (w : List Nat) (bound : ∀ a ∈ w, a < K) :
    (liftWord w bound).length = w.length := by
  have h := congrArg List.length (liftWord_map_val w bound)
  simpa only [List.length_map] using h

theorem infix_of_map_val_infix {K : Nat} {p w : Word K}
    (h : (p.map Fin.val).IsInfix (w.map Fin.val)) : p.IsInfix w := by
  obtain ⟨q, hq, heq⟩ := List.infix_map_iff.mp h
  have hpq : p = q := (List.map_inj_right (fun a b h => Fin.eq_of_val_eq h)).mp heq
  exact hpq.symm ▸ hq

theorem infix_liftWord_iff {K : Nat} (w : List Nat) (bound : ∀ a ∈ w, a < K)
    (p : Word K) : p.IsInfix (liftWord w bound) ↔ (p.map Fin.val).IsInfix w := by
  constructor
  · intro h
    simpa only [liftWord_map_val] using h.map Fin.val
  · intro h
    apply infix_of_map_val_infix
    simpa only [liftWord_map_val] using h

theorem map_val_finRange (K : Nat) : (List.finRange K).map Fin.val = List.range K := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [List.getElem_finRange]

theorem isPermutation_map_val_perm_range {K : Nat} {p : Word K} (hp : IsPermutation p) :
    (p.map Fin.val).Perm (List.range K) := by
  have h := ((isPermutation_iff_perm_finRange p).mp hp).map Fin.val
  simpa only [map_val_finRange] using h

/-- Literal coverage of mapped finite permutations is sufficient for the lift. -/
theorem isSuperpermutation_liftWord_of_mapped_coverage {K : Nat} (w : List Nat)
    (bound : ∀ a ∈ w, a < K)
    (hcover : ∀ p : Word K, IsPermutation p → (p.map Fin.val).IsInfix w) :
    IsSuperpermutation (liftWord w bound) := by
  intro p hp
  exact (infix_liftWord_iff w bound p).mpr (hcover p hp)

/-- A supported natural word covering every permutation of range K gives
the exact finite-alphabet superpermutation required by the theorem contracts. -/
theorem isSuperpermutation_liftWord_of_covers {K : Nat} (w : List Nat)
    (bound : ∀ a ∈ w, a < K) (hcover : CoversPermutationsOf (List.range K) w) :
    IsSuperpermutation (liftWord w bound) := by
  apply isSuperpermutation_liftWord_of_mapped_coverage w bound
  intro p hp
  exact hcover (p.map Fin.val) (isPermutation_map_val_perm_range hp)

theorem hasSuperpermutationOfLengthAtMost_of_supported_nat_word {K B : Nat}
    (w : List Nat) (bound : ∀ a ∈ w, a < K)
    (hcover : CoversPermutationsOf (List.range K) w) (hlen : w.length ≤ B) :
    HasSuperpermutationOfLengthAtMost K B := by
  exact ⟨liftWord w bound, isSuperpermutation_liftWord_of_covers w bound hcover,
    by simpa only [liftWord_length] using hlen⟩

theorem hasSuperpermutationOfLengthAtMost_of_supported_mapped_coverage {K B : Nat}
    (w : List Nat) (bound : ∀ a ∈ w, a < K)
    (hcover : ∀ p : Word K, IsPermutation p → (p.map Fin.val).IsInfix w)
    (hlen : w.length ≤ B) : HasSuperpermutationOfLengthAtMost K B := by
  exact ⟨liftWord w bound, isSuperpermutation_liftWord_of_mapped_coverage w bound hcover,
    by simpa only [liftWord_length] using hlen⟩

end SuperpermutationUpperBound
