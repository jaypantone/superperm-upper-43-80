import SuperpermutationUpperBound.Foundation.Words

/-! Literal row data shared by spelling, seed certificates, and transport.
The old ordinary parameter is `base.length`; the final alphabet size of a row
is one larger. Validity is separate from data so finite certificates reduce
without carrying redundant proof fields. -/
namespace SuperpermutationUpperBound

structure Row (α : Type) where
  base : List α
  satellite : α
  visible : Nat
  deriving DecidableEq, Repr

namespace Row

def Valid (r : Row α) : Prop :=
  r.base.Nodup ∧ r.satellite ∉ r.base ∧ 1 ≤ r.visible ∧ r.visible ≤ r.base.length

instance [DecidableEq α] (r : Row α) : Decidable r.Valid := by
  unfold Valid
  infer_instance

def charge (r : Row α) : Nat := r.base.length - r.visible

def head (r : Row α) : List α := r.base.take (r.base.length - 2)

def tail (r : Row α) : List α :=
  (r.base.rotateLeft (r.visible + 1)).take (r.base.length - 2)

/-- A representative of the j-th visible cyclic class. -/
def entry (r : Row α) (j : Nat) : List α := r.base.rotateLeft j ++ [r.satellite]

/-- Every rotation of every visible entry is an assigned literal permutation. -/
def Assigned (r : Row α) (p : List α) : Prop :=
  ∃ j, j < r.visible ∧ ∃ i, i < r.base.length + 1 ∧ p = (r.entry j).rotateLeft i

def Compatible (r t : Row α) : Prop := r.tail = t.head

end Row

/-- Cyclic base equivalence, with a finite rotation index for kernel checking. -/
def CyclicEq (x y : List α) : Prop :=
  ∃ j : Fin x.length, x.rotateLeft j.val = y

instance [DecidableEq α] (x y : List α) : Decidable (CyclicEq x y) := by
  unfold CyclicEq
  infer_instance

/-- Adjacent compatibility including the final-to-first boundary.
`zip` uses the occurrence order, without identifying equal vertices. -/
def CyclicallyCompatible (rs : List (Row α)) : Prop :=
  ∀ pair ∈ rs.zip (rs.rotateLeft 1), Row.Compatible pair.1 pair.2

/-- Labeled row occurrences are retained even if actual endpoint tuples coincide. -/
def ClosedTrail (rs : List (Row α)) : Prop :=
  rs ≠ [] ∧ CyclicallyCompatible rs

end SuperpermutationUpperBound
