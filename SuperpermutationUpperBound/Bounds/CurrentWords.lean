import SuperpermutationUpperBound.Bounds.CurrentCircleFamily
import SuperpermutationUpperBound.Assembly.CircleRows
import SuperpermutationUpperBound.Assembly.SupportedStates

namespace SuperpermutationUpperBound.Bounds
open Partition

/-- The current circle-covered family supplies one actual word and the full
natural connector/cut ledger before optimizing its component count. -/
theorem current_circle_word_ledger (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 9) :
    ∃ t J : Nat, ∃ w : Word (k + 11), IsSuperpermutation w ∧
      t ≤ selectedCircleCount k ∧
      J ≤ min t ((k + 10).descFactorial (k + 9 - a)) ∧
      w.length = F3 (k + 11) + ((SprintFamily.rows k).map Row.charge).sum +
        (k + 8) * selectedCircleCount k + (k + 7) * t - (k + 9 - a) * (t - J) := by
  let rows := CurrentCircleFamily.completedFamily k
  let circles := CurrentCircleFamily.circles k
  have hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = k + 11 := by
    intro i r hr
    have h := (CurrentCircleFamily.completed_family_valid k i hr).2
    omega
  have hv : ∀ i r, r ∈ rows i → 1 ≤ r.visible :=
    fun i r hr => (CurrentCircleFamily.completed_family_valid k i hr).1.2.2.1
  have hc : CircleTransport.CircleFamilyValid (k + 11 - 3) circles := by
    simpa only [show k + 11 - 3 = k + 8 by omega] using CurrentCircleFamily.circles_valid k
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := exists_word_of_circle_rows rows circles
    (by omega : 4 ≤ k + 11) (by omega : k + 9 - a ≤ k + 11 - 3)
    hlen hv (CurrentCircleFamily.completed_family_closed k) hc
    (CurrentCircleFamily.completed_family_circle_cover k) (SprintFamily.stateAlphabet k)
    (fun c hcc b hb => (SprintFamily.stateAlphabet_mem k b).mpr
      (CurrentCircleFamily.circles_support k c hcc b hb))
    (fun c hcc b hb => (CurrentCircleFamily.circles_support k c hcc b hb).1)
    (fun i r hr => CurrentCircleFamily.completed_family_word_support k i hr)
    (fun _ hp => CurrentCircleFamily.completed_family_cover_range k hp)
  have hi := CurrentCircleFamily.completed_family_univ_inventory k
  have hvisible := (hi.map Row.visible).sum_eq
  have hcount := hi.length_eq
  change (((Finset.univ.toList).flatMap rows).map Row.visible).sum = _ at hvisible
  change ((Finset.univ.toList).flatMap rows).length = _ at hcount
  rw [(SprintFamily.completedRows_counts k).2.1] at hvisible
  rw [(SprintFamily.completedRows_counts k).1] at hcount
  have hcnum : circles.length = selectedCircleCount k := CurrentCircleFamily.circles_count k
  rw [hvisible, hcount, hcnum] at hl
  refine ⟨t, J, w, hw, by rwa [hcnum] at ht,
    by simpa only [SprintFamily.stateAlphabet_card] using hJ, ?_⟩
  rw [hl]
  simp only [F3, show k + 11 - 1 = k + 10 by omega,
    show k + 11 - 2 = k + 9 by omega, show k + 11 - 3 = k + 8 by omega,
    show k + 11 - 4 = k + 7 by omega]
  rw [show (k + 11).factorial = (k + 11) * (k + 10).factorial from Nat.factorial_succ (k + 10)]
  congr 1
  ring

/-- Optimize the module and final trail counts in the actual word ledger. -/
theorem current_circle_word_bound (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 9) :
    ∃ w : Word (k + 11), IsSuperpermutation w ∧
      w.length ≤ F3 (k + 11) + ((SprintFamily.rows k).map Row.charge).sum +
        (k + 8) * selectedCircleCount k + (a - 2) * selectedCircleCount k +
        (k + 9 - a) * min (selectedCircleCount k)
          ((k + 10).descFactorial (k + 9 - a)) := by
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := current_circle_word_ledger k a ha ham
  refine ⟨w, hw, circle_overlap_length_bound (m := k + 9) ha ham ht hJ ?_⟩
  simpa only [show k + 9 - 2 = k + 7 by omega] using hl

end SuperpermutationUpperBound.Bounds
