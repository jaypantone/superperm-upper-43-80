import SuperpermutationUpperBound43.Family
import SuperpermutationUpperBound.Bounds.CircleRational
import SuperpermutationUpperBound.Bounds.AsymptoticEpsilon
import SuperpermutationUpperBound.Assembly.CircleRows
import SuperpermutationUpperBound.Assembly.SupportedStates

namespace SuperpermutationUpperBound43.Bounds

open SuperpermutationUpperBound

set_option maxHeartbeats 2000000

/-- The finite expression for the new partition and 357 selected circles. -/
def bound (m a : Nat) : ℚ :=
  (F3 (m + 2) : ℚ)
    + ((43 : ℚ) / 80) * (Nat.factorial (m - 1) : ℚ)
    + ((a - 2 : Nat) : ℚ) * ((17 : ℚ) / 240) * (Nat.factorial (m - 1) : ℚ)
        / ((m - 1 : Nat) : ℚ)
    + ((m - a : Nat) : ℚ) *
        min (((17 : ℚ) / 240) * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
          ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (a + 1) : ℚ))

def FiniteStatement : Prop :=
  ∀ m : Nat, 9 ≤ m → ∀ a : Nat, 2 ≤ a → a ≤ m →
    ∃ w : Word (m + 2), IsSuperpermutation w ∧ (w.length : ℚ) ≤ bound m a

def AsymptoticStatement : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : Nat, 11 ≤ N ∧
    ∀ K : Nat, N ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 K : ℚ) + ((43 : ℚ) / 80 + ε) * (Fourth K : ℚ)

/-- The integer ledger produced by closed row assembly and overlap joins. -/
def ledger (k a q c : Nat) : Nat :=
  F3 (k + 11) + q + (k + 8) * c + (a - 2) * c +
    (k + 9 - a) * min c ((k + 10).descFactorial (k + 9 - a))

theorem circle_count_scaled (k c : Nat)
    (hc : 5040 * c = 357 * (k + 7).factorial) :
    5040 * ((k + 8) * c) = 357 * (k + 8).factorial := by
  rw [show (k + 8).factorial = (k + 8) * (k + 7).factorial from
    Nat.factorial_succ (k + 7)]
  nlinarith

theorem circle_count_rat (k c : Nat)
    (hc : 5040 * c = 357 * (k + 7).factorial) :
    (c : ℚ) = (17 / 240 : ℚ) * ((k + 8).factorial : ℚ) / (k + 8 : Nat) := by
  have hk : ((k + 8 : Nat) : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hk).mpr
  have he : (5040 : ℚ) * (((k + 8 : Nat) : ℚ) * (c : ℚ)) =
      357 * ((k + 8).factorial : ℚ) := by
    exact_mod_cast circle_count_scaled k c hc
  linarith

theorem principal_numerator (k q c : Nat)
    (hq : 15 * q = 7 * (k + 8).factorial)
    (hc : 5040 * c = 357 * (k + 7).factorial) :
    80 * (q + (k + 8) * c) = 43 * (k + 8).factorial := by
  have he := circle_count_scaled k c hc
  omega

theorem principal_rat (k q c : Nat)
    (hq : 15 * q = 7 * (k + 8).factorial)
    (hc : 5040 * c = 357 * (k + 7).factorial) :
    ((q + (k + 8) * c : Nat) : ℚ) = (43 / 80 : ℚ) * ((k + 8).factorial : ℚ) := by
  have he : (80 : ℚ) * ((q + (k + 8) * c : Nat) : ℚ) =
      43 * ((k + 8).factorial : ℚ) := by
    exact_mod_cast principal_numerator k q c hq hc
  linarith

theorem ledger_eq_bound (k a q c : Nat) (ha : a ≤ k + 9)
    (hq : 15 * q = 7 * (k + 8).factorial)
    (hc : 5040 * c = 357 * (k + 7).factorial) :
    (ledger k a q c : ℚ) = bound (k + 9) a := by
  have hp := principal_rat k q c hq hc
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hp
  unfold ledger bound
  rw [show k + 9 + 2 = k + 11 by omega, show k + 9 - 1 = k + 8 by omega,
    show k + 9 + 1 = k + 10 by omega]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_min, Nat.cast_ofNat]
  rw [show (F3 (k + 11) : ℚ) + (q : ℚ) + ((k : ℚ) + 8) * (c : ℚ) =
      (F3 (k + 11) : ℚ) + (43 / 80 : ℚ) * ((k + 8).factorial : ℚ) by linarith]
  rw [circle_count_rat k c hc,
    SuperpermutationUpperBound.Bounds.overlap_state_count_rat k a ha]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  ring

theorem bound_of_nat_ledger (k a q c len : Nat) (ha : a ≤ k + 9)
    (hq : 15 * q = 7 * (k + 8).factorial)
    (hc : 5040 * c = 357 * (k + 7).factorial)
    (hl : len ≤ ledger k a q c) : (len : ℚ) ≤ bound (k + 9) a := by
  rw [← ledger_eq_bound k a q c ha hq hc]
  exact_mod_cast hl

/-- The final arithmetic conversion takes actual words, with their proved counts. -/
theorem finite_of_nat_ledger
    (hw : ∀ k a : Nat, 2 ≤ a → a ≤ k + 9 →
      ∃ q c : Nat, ∃ w : Word (k + 11), IsSuperpermutation w ∧
        15 * q = 7 * (k + 8).factorial ∧
        5040 * c = 357 * (k + 7).factorial ∧ w.length ≤ ledger k a q c) :
    FiniteStatement := by
  intro m hm a ha ham
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hak : a ≤ k + 9 := by omega
  obtain ⟨q, c, w, hs, hq, hc, hl⟩ := hw k a ha hak
  have he : ∃ w : Word (k + 11), IsSuperpermutation w ∧
      (w.length : ℚ) ≤ bound (k + 9) a :=
    ⟨w, hs, bound_of_nat_ledger k a q c w.length hak hq hc hl⟩
  rw [Nat.add_comm 9 k]
  exact he

/-- The linear-overlap error is at most 2/r, using gamma <= 1. -/
theorem linear_error_le (m a r : Nat) (hm : 2 ≤ m) (hr : 1 ≤ r)
    (har : a * r ≤ m) :
    ((a - 2 : Nat) : ℚ) * ((17 : ℚ) / 240) / ((m - 1 : Nat) : ℚ) ≤
      2 / (r : ℚ) := by
  have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have harQ : (a : ℚ) * r ≤ m := by exact_mod_cast har
  have hd : ((m - 1 : Nat) : ℚ) = (m : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hn : ((a - 2 : Nat) : ℚ) * ((17 : ℚ) / 240) ≤ a := by
    have hsub : ((a - 2 : Nat) : ℚ) ≤ a := by exact_mod_cast Nat.sub_le a 2
    have hmul := mul_le_mul_of_nonneg_left
      (by norm_num : (17 : ℚ) / 240 ≤ 1) (show (0 : ℚ) ≤ ((a - 2 : Nat) : ℚ) by positivity)
    have hm' : ((a - 2 : Nat) : ℚ) * ((17 : ℚ) / 240) ≤ ((a - 2 : Nat) : ℚ) := by
      simpa only [mul_one] using hmul
    exact hm'.trans hsub
  rw [hd]
  apply (div_le_div_iff₀ (by linarith : (0 : ℚ) < (m : ℚ) - 1) hrQ).mpr
  have hnR := mul_le_mul_of_nonneg_right hn (le_of_lt hrQ)
  linarith

/-- With a=floor(m/r), both errors have an explicit elementary majorant. -/
theorem bound_floor_majorant (m r : Nat) (hr : 1 ≤ r) (hm : 8 * r ≤ m) :
    bound m (m / r) ≤
      (F3 (m + 2) : ℚ) +
        ((43 : ℚ) / 80 + 2 / (r : ℚ) + 512 * (r : ℚ) ^ 4 / m) *
          (Fourth (m + 2) : ℚ) := by
  have hb := SuperpermutationUpperBound.Bounds.floor_parameter_bounds m r hr hm
  have hm2 : 2 ≤ m := by omega
  have hlinear := linear_error_le m (m / r) r hm2 hr hb.2.2.1
  have hfactorial := SuperpermutationUpperBound.Bounds.factorial_error_le m (m / r) r (by omega) (by omega) hb.2.2.2
  have hfac : (Nat.factorial (m + 1) : ℚ) =
      ((m : ℚ) + 1) * m * (Nat.factorial (m - 1) : ℚ) := by
    rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (n := m) (by omega)]
    push_cast
    ring
  have htail :
      ((m - m / r : Nat) : ℚ) *
          min (((17 : ℚ) / 240) * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
            ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) ≤
        (m : ℚ) * ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) := by
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.sub_le m (m / r)
  have hFourth : (m + 2) - 3 = m - 1 := by omega
  unfold bound
  rw [Fourth, hFourth]
  calc
    _ ≤ (F3 (m + 2) : ℚ) + ((43 : ℚ) / 80) * (Nat.factorial (m - 1) : ℚ) +
          ((m / r - 2 : Nat) : ℚ) * ((17 : ℚ) / 240) * (Nat.factorial (m - 1) : ℚ)
            / ((m - 1 : Nat) : ℚ) +
          (m : ℚ) * ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) :=
      add_le_add (le_refl _) htail
    _ = (F3 (m + 2) : ℚ) +
          ((43 : ℚ) / 80 +
            ((m / r - 2 : Nat) : ℚ) * ((17 : ℚ) / 240) / ((m - 1 : Nat) : ℚ) +
            (m : ℚ) * m * (m + 1) / (Nat.factorial (m / r + 1) : ℚ)) *
          (Nat.factorial (m - 1) : ℚ) := by
      rw [hfac]
      ring
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact add_le_add (add_le_add (le_refl _) hlinear) hfactorial

/-- The finite circle construction implies the exact rational-epsilon target.
This theorem is conditional on actual finite-parameter word existence. -/
theorem asymptotic_of_finite (hcircle : FiniteStatement) :
    AsymptoticStatement := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt ((4 : ℚ) / ε)
  have hrpos : (0 : ℚ) < r := lt_trans (by positivity) hr
  have hrNat : 1 ≤ r := by exact_mod_cast hrpos
  have hsmall : (2 : ℚ) / r ≤ ε / 2 := by
    apply (div_le_iff₀ hrpos).mpr
    have hh := (div_lt_iff₀ hε).mp hr
    nlinarith
  obtain ⟨M, hM⟩ := exists_nat_gt ((1024 : ℚ) * (r : ℚ) ^ 4 / ε)
  refine ⟨11 + 8 * r + M, by omega, ?_⟩
  intro K hK
  have hm9 : 9 ≤ K - 2 := by omega
  have hmr : 8 * r ≤ K - 2 := by omega
  have hmM : M ≤ K - 2 := by omega
  have hmpos : (0 : ℚ) < ((K - 2 : Nat) : ℚ) := by exact_mod_cast (show 0 < K - 2 by omega)
  have hlarge : 512 * (r : ℚ) ^ 4 / ((K - 2 : Nat) : ℚ) ≤ ε / 2 := by
    apply (div_le_iff₀ hmpos).mpr
    have hbound : (1024 : ℚ) * (r : ℚ) ^ 4 / ε < ((K - 2 : Nat) : ℚ) :=
      hM.trans_le (by exact_mod_cast hmM)
    have hh := (div_lt_iff₀ hε).mp hbound
    nlinarith
  have hb := SuperpermutationUpperBound.Bounds.floor_parameter_bounds (K - 2) r hrNat hmr
  obtain ⟨w, hw, hlen⟩ := hcircle (K - 2) hm9 ((K - 2) / r) (by omega) hb.2.1
  have hlength : (w.length : ℚ) ≤
      (F3 ((K - 2) + 2) : ℚ) +
        ((43 : ℚ) / 80 + ε) * (Fourth ((K - 2) + 2) : ℚ) := by
    apply hlen.trans
    apply (bound_floor_majorant (K - 2) r hrNat hmr).trans
    apply add_le_add (le_refl _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hKeq : K - 2 + 2 = K := by omega
  have hout : ∃ w : Word (K - 2 + 2), IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 (K - 2 + 2) : ℚ) +
        ((43 : ℚ) / 80 + ε) * (Fourth (K - 2 + 2) : ℚ) := ⟨w, hw, hlength⟩
  exact Eq.mp (congrArg (fun n => ∃ w : Word n, IsSuperpermutation w ∧
      (w.length : ℚ) ≤ (F3 n : ℚ) +
        ((43 : ℚ) / 80 + ε) * (Fourth n : ℚ)) hKeq) hout

open SuperpermutationUpperBound.Partition

/-- A certified circle-covered family supplies one actual word and the full
natural connector/cut ledger before optimizing its component count. -/
theorem family_word_ledger {I0 : Type} [Fintype I0] (B : Family.Base I0)
    (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 9) :
    ∃ t J : Nat, ∃ w : Word (k + 11), IsSuperpermutation w ∧
      t ≤ Family.selectedCircleCount k ∧
      J ≤ min t ((k + 10).descFactorial (k + 9 - a)) ∧
      w.length = F3 (k + 11) + ((Family.rows B k).map Row.charge).sum +
        (k + 8) * Family.selectedCircleCount k + (k + 7) * t - (k + 9 - a) * (t - J) := by
  let rows := Family.completedFamily B k
  let circles := Family.circles B k
  have hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = k + 11 := by
    intro i r hr
    have h := (Family.completed_family_valid B k i hr).2
    omega
  have hv : ∀ i r, r ∈ rows i → 1 ≤ r.visible :=
    fun i r hr => (Family.completed_family_valid B k i hr).1.2.2.1
  have hc : CircleTransport.CircleFamilyValid (k + 11 - 3) circles := by
    simpa only [show k + 11 - 3 = k + 8 by omega] using Family.circles_valid B k
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := exists_word_of_circle_rows rows circles
    (by omega : 4 ≤ k + 11) (by omega : k + 9 - a ≤ k + 11 - 3)
    hlen hv (Family.completed_family_closed B k) hc
    (Family.completed_family_circle_cover B k) (SprintFamily.stateAlphabet k)
    (fun c hcc b hb => (SprintFamily.stateAlphabet_mem k b).mpr
      (Family.circles_support B k c hcc b hb))
    (fun c hcc b hb => (Family.circles_support B k c hcc b hb).1)
    (fun i r hr => Family.completed_family_word_support B k i hr)
    (fun _ hp => Family.completed_family_cover_range B k hp)
  have hi := Family.completed_family_univ_inventory B k
  have hvisible := (hi.map Row.visible).sum_eq
  have hcount := hi.length_eq
  change (((Finset.univ.toList).flatMap rows).map Row.visible).sum = _ at hvisible
  change ((Finset.univ.toList).flatMap rows).length = _ at hcount
  rw [(Family.completedRows_counts B k).2.1] at hvisible
  rw [(Family.completedRows_counts B k).1] at hcount
  have hcnum : circles.length = Family.selectedCircleCount k := Family.circles_count B k
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
theorem family_word_bound {I0 : Type} [Fintype I0] (B : Family.Base I0)
    (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 9) :
    ∃ w : Word (k + 11), IsSuperpermutation w ∧
      w.length ≤ F3 (k + 11) + ((Family.rows B k).map Row.charge).sum +
        (k + 8) * Family.selectedCircleCount k + (a - 2) * Family.selectedCircleCount k +
        (k + 9 - a) * min (Family.selectedCircleCount k)
          ((k + 10).descFactorial (k + 9 - a)) := by
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := family_word_ledger B k a ha ham
  refine ⟨w, hw, SuperpermutationUpperBound.Bounds.circle_overlap_length_bound (m := k + 9) ha ham ht hJ ?_⟩
  simpa only [show k + 9 - 2 = k + 7 by omega] using hl

/-- Every semantic base certificate with the stated counts gives the finite bound. -/
theorem finite_of_base {I0 : Type} [Fintype I0] (B : Family.Base I0) : FiniteStatement := by
  apply finite_of_nat_ledger
  intro k a ha ham
  obtain ⟨w, hw, hl⟩ := family_word_bound B k a ha ham
  refine ⟨((Family.rows B k).map Row.charge).sum, Family.selectedCircleCount k,
    w, hw, Family.rows_charge B k, Family.selectedCircleCount_factorial k, ?_⟩
  exact hl

/-- The eventual coefficient follows from the same certified finite base. -/
theorem asymptotic_of_base {I0 : Type} [Fintype I0] (B : Family.Base I0) : AsymptoticStatement :=
  asymptotic_of_finite (finite_of_base B)

/-- The finite conclusion stated with literal words and explicit factorials. -/
theorem finite_of_base_explicit {I0 : Type} [Fintype I0] (B : Family.Base I0)
    (m : Nat) (hm : 9 ≤ m) (a : Nat) (ha : 2 ≤ a) (ham : a ≤ m) :
    ∃ w : Word (m + 2), IsSuperpermutation w ∧
      (w.length : ℚ) ≤
        (((m + 2).factorial + (m + 1).factorial + m.factorial : Nat) : ℚ)
          + (43 / 80 : ℚ) * ((m - 1).factorial : ℚ)
          + ((a - 2 : Nat) : ℚ) * (17 / 240 : ℚ) * ((m - 1).factorial : ℚ)
              / ((m - 1 : Nat) : ℚ)
          + ((m - a : Nat) : ℚ) *
              min ((17 / 240 : ℚ) * ((m - 1).factorial : ℚ) / ((m - 1 : Nat) : ℚ))
                (((m + 1).factorial : ℚ) / ((a + 1).factorial : ℚ)) := by
  simpa only [bound, F3, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] using finite_of_base B m hm a ha ham

/-- The eventual conclusion stated independently of the bound abbreviations. -/
theorem asymptotic_of_base_explicit {I0 : Type} [Fintype I0] (B : Family.Base I0) :
    ∀ ε : ℚ, 0 < ε → ∃ N : Nat, 11 ≤ N ∧
      ∀ K : Nat, N ≤ K → ∃ w : Word K, IsSuperpermutation w ∧
        (w.length : ℚ) ≤
          ((K.factorial + (K - 1).factorial + (K - 2).factorial : Nat) : ℚ)
            + ((43 : ℚ) / 80 + ε) * ((K - 3).factorial : ℚ) := by
  simpa only [AsymptoticStatement, F3, Fourth] using asymptotic_of_base B

end SuperpermutationUpperBound43.Bounds
