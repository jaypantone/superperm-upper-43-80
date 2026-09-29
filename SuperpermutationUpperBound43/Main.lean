import SuperpermutationUpperBound43.Certificate.BasePartition
import SuperpermutationUpperBound43.Certificate.Circles
import SuperpermutationUpperBound43.GenericBounds

namespace SuperpermutationUpperBound43
open SuperpermutationUpperBound

/-- Every field is discharged by the explicit literal partition and cover. -/
def certifiedBase : Family.Base (Fin 350) where
  baseRows := Certificate.rows
  baseLabels := List.finRange 350
  baseFamily := Certificate.family
  baseCircles := Certificate.Circles.circles
  labels_complete := List.mem_finRange
  labels_nodup := List.nodup_finRange 350
  inventory := Certificate.family_inventory
  basedOn := Certificate.rows_basedOn
  complete := Certificate.rows_complete
  row_count := Certificate.rows_count
  charge := Certificate.rows_charge
  closed := fun i => (Certificate.family_closed_winding i).1
  winding := fun i => (Certificate.family_closed_winding i).2
  circles_valid := Certificate.Circles.circles_valid
  circles_support := fun c hc a ha =>
    ⟨Certificate.Circles.circles_support c hc a ha,
      fun he => Certificate.Circles.circles_avoid_satellite c hc (he ▸ ha)⟩
  circle_count := Certificate.Circles.circles_count
  safe_cover := Certificate.Circles.safe_cover

/-- The finite-parameter upper bound for one literal superpermutation. -/
theorem finite_bound (m : Nat) (hm : 9 ≤ m) (a : Nat)
    (ha : 2 ≤ a) (ham : a ≤ m) :
    ∃ w : Word (m + 2), IsSuperpermutation w ∧
      (w.length : ℚ) ≤
        (((m + 2).factorial + (m + 1).factorial + m.factorial : Nat) : ℚ)
          + (43 / 80 : ℚ) * ((m - 1).factorial : ℚ)
          + ((a - 2 : Nat) : ℚ) * (17 / 240 : ℚ) * ((m - 1).factorial : ℚ)
              / ((m - 1 : Nat) : ℚ)
          + ((m - a : Nat) : ℚ) *
              min ((17 / 240 : ℚ) * ((m - 1).factorial : ℚ) / ((m - 1 : Nat) : ℚ))
                (((m + 1).factorial : ℚ) / ((a + 1).factorial : ℚ)) :=
  Bounds.finite_of_base_explicit certifiedBase m hm a ha ham

/-- The same finite bound with its parameter quantified over the integers. -/
theorem finite_bound_integer (m : Nat) (hm : 9 ≤ m) (a : ℤ)
    (ha : 2 ≤ a) (ham : a ≤ (m : ℤ)) :
    ∃ w : Word (m + 2), IsSuperpermutation w ∧
      (w.length : ℚ) ≤
        (((m + 2).factorial + (m + 1).factorial + m.factorial : Nat) : ℚ)
          + (43 / 80 : ℚ) * ((m - 1).factorial : ℚ)
          + ((a : ℚ) - 2) * (17 / 240 : ℚ) * ((m - 1).factorial : ℚ)
              / ((m - 1 : Nat) : ℚ)
          + ((m : ℚ) - (a : ℚ)) *
              min ((17 / 240 : ℚ) * ((m - 1).factorial : ℚ) / ((m - 1 : Nat) : ℚ))
                (((m + 1).factorial : ℚ) / ((a.toNat + 1).factorial : ℚ)) := by
  have ha0 : 0 ≤ a := by omega
  have haeq : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
  have haN : 2 ≤ a.toNat := by omega
  have hamN : a.toNat ≤ m := by omega
  have hcast : (a.toNat : ℚ) = (a : ℚ) := by exact_mod_cast haeq
  obtain ⟨w, hw, hl⟩ := finite_bound m hm a.toNat haN hamN
  refine ⟨w, hw, ?_⟩
  rw [Nat.cast_sub haN, Nat.cast_sub hamN, hcast] at hl
  simpa only [Nat.cast_ofNat] using hl

/-- The eventual rational-epsilon coefficient bound. -/
theorem asymptotic4380 :
    ∀ ε : ℚ, 0 < ε → ∃ N : Nat, 11 ≤ N ∧
      ∀ K : Nat, N ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
        (w.length : ℚ) ≤
          ((K.factorial + (K - 1).factorial + (K - 2).factorial : Nat) : ℚ)
            + ((43 : ℚ) / 80 + ε) * ((K - 3).factorial : ℚ) :=
  Bounds.asymptotic_of_base_explicit certifiedBase

end SuperpermutationUpperBound43
