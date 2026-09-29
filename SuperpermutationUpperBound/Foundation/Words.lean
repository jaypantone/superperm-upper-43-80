import Std

/-!
Literal word semantics for the upper-bound formalization.

The alphabet is zero-based. A duplicate-free list of length n over Fin n
contains each of the n alphabet symbols exactly once. Coverage means
contiguous occurrence of every such list in one finite word.
-/

namespace SuperpermutationUpperBound

abbrev Word (n : Nat) := List (Fin n)

def IsPermutation {n : Nat} (p : Word n) : Prop :=
  p.length = n ∧ p.Nodup

/-- Every required permutation occurs as a contiguous factor. -/
def IsSuperpermutation {n : Nat} (w : Word n) : Prop :=
  ∀ p : Word n, IsPermutation p → p.IsInfix w

/-- An upper bound is an existential assertion about an actual word. -/
def HasSuperpermutationOfLengthAtMost (n bound : Nat) : Prop :=
  ∃ w : Word n, IsSuperpermutation w ∧ w.length ≤ bound

theorem isSuperpermutation_of_infix {n : Nat} {u v : Word n}
    (hu : IsSuperpermutation u) (h : u.IsInfix v) : IsSuperpermutation v := by
  intro p hp
  exact (hu p hp).trans h

theorem isSuperpermutation_append_right {n : Nat} {u : Word n}
    (hu : IsSuperpermutation u) (v : Word n) : IsSuperpermutation (u ++ v) := by
  exact isSuperpermutation_of_infix hu List.infix_append_left

theorem isSuperpermutation_append_left {n : Nat} (u : Word n) {v : Word n}
    (hv : IsSuperpermutation v) : IsSuperpermutation (u ++ v) := by
  exact isSuperpermutation_of_infix hv List.infix_append_right

/-- Separate pieces collectively covering all factors can be concatenated. -/
theorem isSuperpermutation_flatten {n : Nat} (pieces : List (Word n))
    (h : ∀ p : Word n, IsPermutation p →
      ∃ piece ∈ pieces, p.IsInfix piece) :
    IsSuperpermutation pieces.flatten := by
  intro p hp
  obtain ⟨piece, hmem, hfactor⟩ := h p hp
  exact hfactor.trans (List.infix_of_mem_flatten hmem)

end SuperpermutationUpperBound
