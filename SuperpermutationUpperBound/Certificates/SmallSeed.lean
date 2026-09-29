import SuperpermutationUpperBound.Rows
import SuperpermutationUpperBound.Foundation.Rotation

/-! Kernel-checked six-letter seeds.  The walk, deficits and block relation
are the literal row data used by transport, not a separate Boolean model. -/
namespace SuperpermutationUpperBound.Certificates.SmallSeed

abbrev Letter := Fin 7

/-- Full-row successor at old ordinary size six. -/
def fullStep : List Letter → List Letter
  | [a, b, c, d, e, f] => [b, c, d, e, a, f]
  | p => p

/-- Deficit-two successor at old ordinary size six. -/
def shortStep : List Letter → List Letter
  | [a, b, c, d, e, f] => [f, a, b, c, e, d]
  | p => p

/-- The next base uses the deficit of the row just emitted. -/
def walk (start : List Letter) : List Nat → List (Row Letter)
  | [] => []
  | d :: ds =>
    ⟨start, 6, 6 - d⟩ :: walk (if d = 2 then shortStep start else fullStep start) ds

def deficits : List Nat := [2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0]

def starts : List (List Letter) :=
  [[0, 1, 2, 3, 4, 5], [0, 1, 4, 5, 2, 3], [0, 2, 1, 4, 3, 5],
   [0, 4, 1, 2, 5, 3], [1, 0, 2, 3, 5, 4], [1, 0, 4, 5, 3, 2]]

def seed : List (Row Letter) := walk [0, 1, 2, 3, 4, 5] deficits

def seeds : List (List (Row Letter)) := starts.map (fun p => walk p deficits)

def allRows : List (Row Letter) := seeds.flatten

instance (rs : List (Row Letter)) : Decidable (CyclicallyCompatible rs) := by
  unfold CyclicallyCompatible Row.Compatible
  infer_instance

instance (rs : List (Row Letter)) : Decidable (ClosedTrail rs) := by
  unfold ClosedTrail
  infer_instance

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The advertised start and short/full deficit pattern. -/
theorem seed_length : seed.length = 16 := by decide

theorem seed_valid : ∀ r ∈ seed, r.Valid := by decide

theorem seed_base_length : ∀ r ∈ seed, r.base.length = 6 := by decide

theorem seed_deficits : ∀ r ∈ seed, r.charge = 0 ∨ r.charge = 2 := by decide

theorem seed_charge : (seed.map Row.charge).sum = 8 := by decide

theorem seed_visible : (seed.map Row.visible).sum = 88 := by decide

theorem seed_closed : ClosedTrail seed := by decide

/-- Distinctness is in the semantic rotation relation used by the construction. -/
theorem seed_distinct_blocks :
    seed.Pairwise (fun r s => ¬ CyclicEq r.base s.base) := by decide

theorem seed_entries_permutations :
    ∀ r ∈ seed, ∀ j : Fin r.visible, IsPermutation (r.entry j.val) := by
  unfold IsPermutation
  decide

theorem seed_assigned_permutations {r : Row Letter} (hr : r ∈ seed)
    {p : Word 7} (hp : r.Assigned p) : IsPermutation p := by
  obtain ⟨j, hj, i, _, rfl⟩ := hp
  exact isPermutation_rot (seed_entries_permutations r hr ⟨j, hj⟩) i

theorem seeds_length : seeds.length = 6 := by decide

theorem seeds_row_counts : ∀ rs ∈ seeds, rs.length = 16 := by decide

theorem seeds_charges : ∀ rs ∈ seeds, (rs.map Row.charge).sum = 8 := by decide

theorem seeds_closed : ∀ rs ∈ seeds, ClosedTrail rs := by decide

theorem allRows_length : allRows.length = 96 := by decide

theorem allRows_valid : ∀ r ∈ allRows, r.Valid := by decide

theorem allRows_base_length : ∀ r ∈ allRows, r.base.length = 6 := by decide

theorem allRows_deficits : ∀ r ∈ allRows, r.charge = 0 ∨ r.charge = 2 := by decide

theorem allRows_charge : (allRows.map Row.charge).sum = 48 := by decide

theorem allRows_visible : (allRows.map Row.visible).sum = 528 := by decide

theorem allRows_distinct_blocks :
    allRows.Pairwise (fun r s => ¬ CyclicEq r.base s.base) := by decide

theorem allRows_entries_permutations :
    ∀ r ∈ allRows, ∀ j : Fin r.visible, IsPermutation (r.entry j.val) := by
  unfold IsPermutation
  decide

theorem allRows_assigned_permutations {r : Row Letter} (hr : r ∈ allRows)
    {p : Word 7} (hp : r.Assigned p) : IsPermutation p := by
  obtain ⟨j, hj, i, _, rfl⟩ := hp
  exact isPermutation_rot (allRows_entries_permutations r hr ⟨j, hj⟩) i

/-- Complete first finite milestone in one kernel-checked proposition. -/
theorem seed_certificate :
    seed.length = 16 ∧
    (∀ r ∈ seed, r.Valid ∧ r.base.length = 6 ∧ (r.charge = 0 ∨ r.charge = 2)) ∧
    ClosedTrail seed ∧
    seed.Pairwise (fun r s => ¬ CyclicEq r.base s.base) ∧
    (seed.map Row.charge).sum = 8 ∧ (seed.map Row.visible).sum = 88 ∧
    (∀ r ∈ seed, ∀ p, r.Assigned p → IsPermutation p) := by
  refine ⟨seed_length, ?_, seed_closed, seed_distinct_blocks, seed_charge, seed_visible, ?_⟩
  · intro r hr
    exact ⟨seed_valid r hr, seed_base_length r hr, seed_deficits r hr⟩
  · intro r hr p hp
    exact seed_assigned_permutations hr hp

/-- The six original closed seeds occupy 96 different cyclic base blocks. -/
theorem six_seed_certificate :
    seeds.length = 6 ∧
    (∀ rs ∈ seeds, rs.length = 16 ∧ ClosedTrail rs ∧ (rs.map Row.charge).sum = 8) ∧
    allRows.length = 96 ∧
    (∀ r ∈ allRows, r.Valid ∧ r.base.length = 6 ∧ (r.charge = 0 ∨ r.charge = 2)) ∧
    allRows.Pairwise (fun r s => ¬ CyclicEq r.base s.base) ∧
    (allRows.map Row.charge).sum = 48 ∧ (allRows.map Row.visible).sum = 528 ∧
    (∀ r ∈ allRows, ∀ p, r.Assigned p → IsPermutation p) := by
  refine ⟨seeds_length, ?_, allRows_length, ?_, allRows_distinct_blocks,
    allRows_charge, allRows_visible, ?_⟩
  · intro rs hrs
    exact ⟨seeds_row_counts rs hrs, seeds_closed rs hrs, seeds_charges rs hrs⟩
  · intro r hr
    exact ⟨allRows_valid r hr, allRows_base_length r hr, allRows_deficits r hr⟩
  · intro r hr p hp
    exact allRows_assigned_permutations hr hp

#print axioms seed_length
#print axioms seed_valid
#print axioms seed_base_length
#print axioms seed_deficits
#print axioms seed_charge
#print axioms seed_visible
#print axioms seed_closed
#print axioms seed_distinct_blocks
#print axioms seed_entries_permutations
#print axioms seed_assigned_permutations
#print axioms seeds_length
#print axioms seeds_row_counts
#print axioms seeds_charges
#print axioms seeds_closed
#print axioms allRows_length
#print axioms allRows_valid
#print axioms allRows_base_length
#print axioms allRows_deficits
#print axioms allRows_charge
#print axioms allRows_visible
#print axioms allRows_distinct_blocks
#print axioms allRows_entries_permutations
#print axioms allRows_assigned_permutations
#print axioms seed_certificate
#print axioms six_seed_certificate

end SuperpermutationUpperBound.Certificates.SmallSeed
