import SuperpermutationUpperBound.Foundation.Words

/-! Enumeration and alphabet-relabeling bridges for literal word coverage. -/

namespace SuperpermutationUpperBound

variable {α : Type u} {β : Type v}

/-- A duplicate-free subalphabet of equal length is an actual permutation. -/
theorem perm_of_nodup_subset_length {p q : List α}
    (hp : p.Nodup) (hsub : p ⊆ q) (hlen : p.length = q.length) : p.Perm q := by
  induction p generalizing q with
  | nil =>
    have hq : q = [] := List.length_eq_zero_iff.mp hlen.symm
    subst q
    exact List.Perm.refl []
  | cons a p ih =>
    have ha : a ∈ q := hsub List.mem_cons_self
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hp
    obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
    have htail : p.Perm (s ++ t) := by
      apply ih hnodup
      · intro b hb
        have hne : b ≠ a := by
          intro heq
          subst b
          exact hnot hb
        simpa only [List.mem_append, List.mem_cons, hne, false_or] using
          hsub (List.mem_cons_of_mem a hb)
      · simp only [List.length_cons, List.length_append] at hlen ⊢
        omega
    exact (htail.cons a).trans List.perm_middle.symm

theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij heq
  have hval := congrArg Fin.val heq
  simp [List.getElem_finRange] at hval
  omega

/-- The length-and-no-duplicates definition lists exactly the finite alphabet. -/
theorem isPermutation_iff_perm_finRange {n : Nat} (p : Word n) :
    IsPermutation p ↔ p.Perm (List.finRange n) := by
  constructor
  · intro hp
    exact perm_of_nodup_subset_length hp.2
      (fun a _ => List.mem_finRange a) (by simpa using hp.1)
  · intro hp
    exact ⟨by simpa using hp.length_eq, hp.symm.nodup (nodup_finRange n)⟩

/-- All literal permutations of a specified alphabet occur as factors. -/
def CoversPermutationsOf (alphabet w : List α) : Prop :=
  ∀ p : List α, p.Perm alphabet → p.IsInfix w

theorem coversPermutationsOf_finRange_iff {n : Nat} (w : Word n) :
    CoversPermutationsOf (List.finRange n) w ↔ IsSuperpermutation w := by
  constructor
  · intro h p hp
    exact h p ((isPermutation_iff_perm_finRange p).mp hp)
  · intro h p hp
    exact h p ((isPermutation_iff_perm_finRange p).mpr hp)

theorem map_map_of_leftInverse (f : α → β) (g : β → α)
    (hgf : ∀ a, g (f a) = a) (x : List α) : (x.map f).map g = x := by
  induction x with
  | nil => rfl
  | cons a x ih => simp [hgf, ih]

/-- Explicit inverse maps transfer complete literal coverage between alphabets. -/
theorem CoversPermutationsOf.map_bijection {alphabet w : List α}
    (hw : CoversPermutationsOf alphabet w) (f : α → β) (g : β → α)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) :
    CoversPermutationsOf (alphabet.map f) (w.map f) := by
  intro p hp
  have hback : (p.map g).Perm alphabet := by
    have h := hp.map g
    simpa only [map_map_of_leftInverse f g hgf] using h
  have hfactor := (hw (p.map g) hback).map f
  simpa only [map_map_of_leftInverse g f hfg] using hfactor

theorem CoversPermutationsOf.congr_alphabet {alphabet alphabet' w : List α}
    (hw : CoversPermutationsOf alphabet w) (ha : alphabet.Perm alphabet') :
    CoversPermutationsOf alphabet' w := by
  intro p hp
  exact hw p (hp.trans ha.symm)

theorem coversPermutationsOf_map_bijection_iff (alphabet w : List α)
    (f : α → β) (g : β → α)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) :
    CoversPermutationsOf (alphabet.map f) (w.map f) ↔
      CoversPermutationsOf alphabet w := by
  constructor
  · intro h
    have hback := h.map_bijection g f hfg hgf
    simpa only [map_map_of_leftInverse f g hgf] using hback
  · intro h
    exact h.map_bijection f g hgf hfg

/-- Convert coverage on a generic alphabet into the project's finite-word semantics. -/
theorem CoversPermutationsOf.isSuperpermutation_map {n : Nat} {alphabet w : List α}
    (hw : CoversPermutationsOf alphabet w) (f : α → Fin n) (g : Fin n → α)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b)
    (ha : (alphabet.map f).Perm (List.finRange n)) :
    IsSuperpermutation (w.map f) := by
  exact (coversPermutationsOf_finRange_iff _).mp
    ((hw.map_bijection f g hgf hfg).congr_alphabet ha)

@[simp] theorem relabel_length (f : α → β) (w : List α) : (w.map f).length = w.length :=
  List.length_map f

end SuperpermutationUpperBound
