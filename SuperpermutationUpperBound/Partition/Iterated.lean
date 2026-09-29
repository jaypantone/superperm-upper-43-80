import SuperpermutationUpperBound.Partition.Basic

/-! Arbitrarily many fresh-letter transports preserve the exact partition of
cyclic base blocks. These theorems concern row occurrences and block coverage;
the additional closed-component structure is proved separately. -/
namespace SuperpermutationUpperBound.Partition

variable {α : Type}

def FreshLetters (alphabet : List α) (s : α) : List α → Prop
  | [] => True
  | z :: zs => z ∉ alphabet ∧ z ≠ s ∧ FreshLetters (z :: alphabet) s zs

def extendAlphabet (alphabet : List α) : List α → List α
  | [] => alphabet
  | z :: zs => extendAlphabet (z :: alphabet) zs

def iteratedRows (rs : List (Row α)) : List α → List (Row α)
  | [] => rs
  | z :: zs => iteratedRows (Transport.packingRows rs z) zs

theorem extendAlphabet_length (alphabet zs : List α) :
    (extendAlphabet alphabet zs).length = alphabet.length + zs.length := by
  induction zs generalizing alphabet with
  | nil => simp [extendAlphabet]
  | cons z zs ih =>
    simp only [extendAlphabet, ih, List.length_cons]
    omega

/-- Exact partition preservation for any finite sequence of fresh letters. -/
theorem iteratedRows_partition [DecidableEq α] {alphabet : List α} {s : α}
    {rs : List (Row α)} (ha : alphabet.Nodup) (hne : alphabet ≠ [])
    (hb : BasedOn alphabet s rs) (hc : BlockComplete alphabet rs)
    (hd : DistinctBlocks rs) (zs : List α) (hzs : FreshLetters alphabet s zs) :
    BasedOn (extendAlphabet alphabet zs) s (iteratedRows rs zs) ∧
    BlockComplete (extendAlphabet alphabet zs) (iteratedRows rs zs) ∧
    DistinctBlocks (iteratedRows rs zs) := by
  induction zs generalizing alphabet rs with
  | nil => exact ⟨hb, hc, hd⟩
  | cons z zs ih =>
    exact ih (List.nodup_cons.mpr ⟨hzs.1, ha⟩) (by simp)
      (hb.transport hzs.1 hzs.2.1) (hc.transport hb ha hne hzs.1)
      (hd.transport hb hzs.1) hzs.2.2

/-- A rational charge ratio is recorded without natural-number division. -/
def ChargeRatio (numerator denominator : Nat) (rs : List (Row α)) : Prop :=
  denominator * (rs.map Row.charge).sum = numerator * rs.length

theorem chargeRatio_transport {alphabet : List α} {s z : α} {rs : List (Row α)}
    {a b : Nat} (hb : BasedOn alphabet s rs) (hz : z ∉ alphabet) (hzs : z ≠ s)
    (hr : ChargeRatio a b rs) : ChargeRatio a b (Transport.packingRows rs z) := by
  have hc := Transport.packingRows_counts rs z alphabet.length (hb.ready hz hzs)
  unfold ChargeRatio at *
  rw [hc.1, hc.2.1, Nat.mul_left_comm b, Nat.mul_left_comm a, hr]

theorem iteratedRows_chargeRatio {alphabet : List α} {s : α} {rs : List (Row α)}
    {a b : Nat} (hb : BasedOn alphabet s rs) (hr : ChargeRatio a b rs)
    (zs : List α) (hzs : FreshLetters alphabet s zs) :
    ChargeRatio a b (iteratedRows rs zs) := by
  induction zs generalizing alphabet rs with
  | nil => exact hr
  | cons z zs ih =>
    exact ih (hb.transport hzs.1 hzs.2.1)
      (chargeRatio_transport hb hzs.1 hzs.2.1 hr) hzs.2.2

def transportMultiplier (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => n * transportMultiplier (n + 1) k

theorem iteratedRows_counts {alphabet : List α} {s : α} {rs : List (Row α)}
    (hb : BasedOn alphabet s rs) (zs : List α) (hzs : FreshLetters alphabet s zs) :
    (iteratedRows rs zs).length = transportMultiplier alphabet.length zs.length * rs.length ∧
    ((iteratedRows rs zs).map Row.charge).sum =
      transportMultiplier alphabet.length zs.length * (rs.map Row.charge).sum := by
  induction zs generalizing alphabet rs with
  | nil => simp [iteratedRows, transportMultiplier]
  | cons z zs ih =>
    have ht := ih (hb.transport hzs.1 hzs.2.1) hzs.2.2
    have hc := Transport.packingRows_counts rs z alphabet.length (hb.ready hzs.1 hzs.2.1)
    dsimp only [iteratedRows]
    rw [ht.1, ht.2, hc.1, hc.2.1]
    simp only [List.length_cons, transportMultiplier]
    constructor <;> simp only [Nat.mul_assoc, Nat.mul_left_comm]

end SuperpermutationUpperBound.Partition
