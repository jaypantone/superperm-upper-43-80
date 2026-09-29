import SuperpermutationUpperBound.Rows

/-! Abstract signed port translations.  This module proves their algebra and
the charge-minus-row-count ledger.  Identification with literal local port
paths and the enumeration of closed descendants are separate obligations. -/
namespace SuperpermutationUpperBound.Transport

/-- Translation on a nonempty cyclic port set, using the nonnegative integer
remainder.  The actual modulus is `h + 1`. -/
def shiftPort (h : Nat) (d : Int) (p : Fin (h + 1)) : Fin (h + 1) :=
  ⟨(((p.val : Int) + d) % ((h + 1 : Nat) : Int)).toNat, by
    apply (Int.toNat_lt (Int.emod_nonneg _ (by omega))).mpr
    exact Int.emod_lt_of_pos _ (by omega)⟩

/-- The integer representative of a translated port is the Euclidean remainder. -/
theorem shiftPort_val (h : Nat) (d : Int) (p : Fin (h + 1)) :
    ((shiftPort h d p).val : Int) = ((p.val : Int) + d) % ((h + 1 : Nat) : Int) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

@[simp] theorem shiftPort_zero (h : Nat) (p : Fin (h + 1)) : shiftPort h 0 p = p := by
  apply Fin.ext
  dsimp [shiftPort]
  rw [Int.add_zero, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

/-- Successive displacements compose by integer addition, including negatives. -/
theorem shiftPort_add (h : Nat) (d e : Int) (p : Fin (h + 1)) :
    shiftPort h e (shiftPort h d p) = shiftPort h (d + e) p := by
  apply Fin.ext
  dsimp [shiftPort]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.emod_add_emod, Int.add_assoc]

@[simp] theorem shiftPort_inverse (h : Nat) (d : Int) (p : Fin (h + 1)) :
    shiftPort h (-d) (shiftPort h d p) = p := by
  rw [shiftPort_add]
  rw [Int.add_right_neg, shiftPort_zero]

@[simp] theorem shiftPort_inverse_right (h : Nat) (d : Int) (p : Fin (h + 1)) :
    shiftPort h d (shiftPort h (-d) p) = p := by
  rw [shiftPort_add]
  rw [Int.add_left_neg, shiftPort_zero]

theorem shiftPort_leftInverse (h : Nat) (d : Int) :
    Function.LeftInverse (shiftPort h (-d)) (shiftPort h d) := shiftPort_inverse h d

theorem shiftPort_injective (h : Nat) (d : Int) {p q : Fin (h + 1)}
    (hpq : shiftPort h d p = shiftPort h d q) : p = q := by
  have hh := congrArg (shiftPort h (-d)) hpq
  simpa using hh

theorem shiftPort_surjective (h : Nat) (d : Int) (q : Fin (h + 1)) :
    ∃ p, shiftPort h d p = q :=
  ⟨shiftPort h (-d) q, shiftPort_inverse_right h d q⟩

/-- Explicit bijectivity contract, with the inverse given by displacement `-d`. -/
theorem shiftPort_bijective (h : Nat) (d : Int) :
    (∀ p q, shiftPort h d p = shiftPort h d q → p = q) ∧
    (∀ q, ∃ p, shiftPort h d p = q) :=
  ⟨fun _ _ hpq => shiftPort_injective h d hpq, shiftPort_surjective h d⟩

/-- Follow signed steps in occurrence order. -/
def walkPorts (h : Nat) : List Int → Fin (h + 1) → Fin (h + 1)
  | [], p => p
  | d :: ds, p => walkPorts h ds (shiftPort h d p)

/-- The composite depends only on the integer sum of its displacements. -/
theorem walkPorts_eq_shift (h : Nat) (ds : List Int) (p : Fin (h + 1)) :
    walkPorts h ds p = shiftPort h ds.sum p := by
  induction ds generalizing p with
  | nil => simp [walkPorts]
  | cons d ds ih =>
    rw [walkPorts, ih, shiftPort_add, List.sum_cons]

variable {α : Type}

/-- Full rows have displacement -1; deficit-two rows have displacement +1. -/
def delta (r : Row α) : Int := (r.charge : Int) - 1

@[simp] theorem delta_full {r : Row α} (hr : r.charge = 0) : delta r = -1 := by
  simp [delta, hr]

@[simp] theorem delta_short {r : Row α} (hr : r.charge = 2) : delta r = 1 := by
  simp [delta, hr]

/-- Cast before subtracting: this ledger preserves negative signed excess. -/
theorem sum_delta (rs : List (Row α)) :
    (rs.map delta).sum = ((rs.map Row.charge).sum : Int) - (rs.length : Int) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, delta, Int.natCast_add,
      Int.natCast_one]
    omega

/-- The abstract return map associated with the row occurrences. -/
def rowMonodromy (h : Nat) (rs : List (Row α)) : Fin (h + 1) → Fin (h + 1) :=
  walkPorts h (rs.map delta)

/-- Algebraic monodromy is translation by q-r, using integer subtraction. -/
theorem rowMonodromy_eq_shift (h : Nat) (rs : List (Row α)) (p : Fin (h + 1)) :
    rowMonodromy h rs p =
      shiftPort h (((rs.map Row.charge).sum : Int) - (rs.length : Int)) p := by
  rw [rowMonodromy, walkPorts_eq_shift, sum_delta]

/-- The signed-excess form agrees with translation by the negative of r-q. -/
theorem rowMonodromy_eq_negative_excess (h : Nat) (rs : List (Row α))
    (p : Fin (h + 1)) :
    rowMonodromy h rs p =
      shiftPort h (-((rs.length : Int) - ((rs.map Row.charge).sum : Int))) p := by
  rw [rowMonodromy_eq_shift]
  congr 1
  omega

theorem rowMonodromy_bijective (h : Nat) (rs : List (Row α)) :
    (∀ p q, rowMonodromy h rs p = rowMonodromy h rs q → p = q) ∧
    (∀ q, ∃ p, rowMonodromy h rs p = q) := by
  simp only [rowMonodromy_eq_shift]
  exact shiftPort_bijective h _

#print axioms shiftPort_val
#print axioms shiftPort_zero
#print axioms shiftPort_add
#print axioms shiftPort_inverse
#print axioms shiftPort_bijective
#print axioms walkPorts_eq_shift
#print axioms sum_delta
#print axioms rowMonodromy_eq_shift
#print axioms rowMonodromy_eq_negative_excess
#print axioms rowMonodromy_bijective

end SuperpermutationUpperBound.Transport
