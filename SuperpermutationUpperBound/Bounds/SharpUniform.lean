import SuperpermutationUpperBound.Bounds.GeneralCircle
import SuperpermutationUpperBound.Bounds.StructuralTen
import SuperpermutationUpperBound.Bounds.UniformCircle
import SuperpermutationUpperBound.Certificates.Word8
import SuperpermutationUpperBound.Certificates.Word9

namespace SuperpermutationUpperBound.Bounds

/-- The uniform three-fifths fourth-factorial bound, including size ten. -/
theorem uniform_three_fifths :
    ∀ K : Nat, 10 ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
      5 * w.length ≤ 5 * F3 K + 3 * Fourth K :=
  uniformThreeFifths_of_circleBound_and_structural10 general_circle_bound
    StructuralTen.exists_superpermutation

/-- The uniform 101/120 bound from size eight, with the exact finite base words. -/
theorem uniform_101_over_120 :
    ∀ K : Nat, 8 ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
      120 * w.length ≤ 120 * F3 K + 101 * Fourth K :=
  uniform101Over120_of_finite_and_threeFifths Certificates.Word8.word8_46181
    Certificates.Word9.word9_408743 uniform_three_fifths

#print axioms uniform_three_fifths
#print axioms uniform_101_over_120

end SuperpermutationUpperBound.Bounds
