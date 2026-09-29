import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup

namespace SuperpermutationUpperBound

/-- Literal overlap states are ordered lists of distinct alphabet symbols. -/
def overlapState (n ell : Nat) :=
  {v : List (Fin n) // v.length = ell ∧ v.Nodup}

instance (n ell : Nat) : DecidableEq (overlapState n ell) :=
  inferInstanceAs (DecidableEq {v : List (Fin n) // v.length = ell ∧ v.Nodup})

def embeddingOverlapState (n ell : Nat) (f : Fin ell ↪ Fin n) : overlapState n ell :=
  ⟨List.ofFn f, List.length_ofFn, List.nodup_ofFn_ofInjective f.injective⟩

theorem embeddingOverlapState_bijective (n ell : Nat) :
    Function.Bijective (embeddingOverlapState n ell) := by
  constructor
  · intro f g he
    apply DFunLike.ext'
    exact List.ofFn_injective (congrArg Subtype.val he)
  · rintro ⟨v, hv, hn⟩
    subst ell
    let f : Fin v.length ↪ Fin n := ⟨v.get, fun _ _ he => hn.get_inj_iff.mp he⟩
    refine ⟨f, Subtype.ext ?_⟩
    exact List.ofFn_get v

/-- Lists with the required length and no duplicate letters are equivalent
to injections from the positions into the alphabet. -/
noncomputable def overlapStateEquivEmbedding (n ell : Nat) :
    overlapState n ell ≃ (Fin ell ↪ Fin n) :=
  (Equiv.ofBijective (embeddingOverlapState n ell) (embeddingOverlapState_bijective n ell)).symm

noncomputable instance (n ell : Nat) : Fintype (overlapState n ell) :=
  Fintype.ofEquiv (Fin ell ↪ Fin n) (overlapStateEquivEmbedding n ell).symm

theorem overlapState_card (n ell : Nat) :
    Fintype.card (overlapState n ell) = n.descFactorial ell := by
  rw [Fintype.card_congr (overlapStateEquivEmbedding n ell)]
  simp only [Fintype.card_embedding_eq, Fintype.card_fin]

/-- The exact factorial state count, in a form avoiding natural division. -/
theorem overlapState_card_factorial (n ell : Nat) (hle : ell ≤ n) :
    (n - ell).factorial * Fintype.card (overlapState n ell) = n.factorial := by
  rw [overlapState_card]
  exact Nat.factorial_mul_descFactorial hle

theorem overlapState_card_div (n ell : Nat) (hle : ell ≤ n) :
    Fintype.card (overlapState n ell) = n.factorial / (n - ell).factorial := by
  rw [overlapState_card]
  exact Nat.descFactorial_eq_div hle

/-- The overlap length used by the circle bound leaves `a+1` unused symbols. -/
theorem overlapState_circle_card (m a : Nat) (ha : a ≤ m) :
    Fintype.card (overlapState (m + 1) (m - a)) =
      (m + 1).factorial / (a + 1).factorial := by
  rw [overlapState_card_div _ _ (by omega)]
  rw [show m + 1 - (m - a) = a + 1 by omega]

theorem overlapState_circle_card_factorial (m a : Nat) (ha : a ≤ m) :
    (a + 1).factorial * Fintype.card (overlapState (m + 1) (m - a)) =
      (m + 1).factorial := by
  have hc := overlapState_card_factorial (m + 1) (m - a) (by omega)
  simpa only [show m + 1 - (m - a) = a + 1 by omega] using hc

end SuperpermutationUpperBound
