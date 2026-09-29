import SuperpermutationUpperBound.Bounds.CurrentWords
import SuperpermutationUpperBound.Bounds.CircleRational
import SuperpermutationUpperBound.Bounds.AsymptoticEpsilon

namespace SuperpermutationUpperBound.Bounds

/-- The exact current finite-parameter upper bound, with an actual word. -/
theorem general_circle_bound : CircleBoundStatement :=
  circleBoundStatement_of_nat_ledger current_circle_word_bound

/-- The eventual coefficient of the fourth factorial term, for every positive
rational epsilon and with the explicit lower threshold of eleven symbols. -/
theorem asymptotic2729 :
    ∀ ε : ℚ, 0 < ε → ∃ N : Nat, 11 ≤ N ∧
      ∀ K : Nat, N ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
        (w.length : ℚ) ≤ (F3 K : ℚ) + ((2729 : ℚ) / 5040 + ε) * (Fourth K : ℚ) :=
  asymptotic2729_of_circleBound general_circle_bound

#print axioms general_circle_bound
#print axioms asymptotic2729

end SuperpermutationUpperBound.Bounds
