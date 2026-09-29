import SuperpermutationUpperBound.Foundation.RowRelabeling
import SuperpermutationUpperBound.Partition.SeedBase

/-! The six checked seed trails on natural-number letters. These are precisely
the 96 original seed rows used by SeedBase, retaining their six closed trails.
The additional 24 block-accounting rows are not included in this trail claim. -/
namespace SuperpermutationUpperBound.Certificates.NatSeeds

/-- Relabel each of the six occurrence lists by the literal value of its letters. -/
def trails : List (List (Row Nat)) :=
  SmallSeed.seeds.map (fun rs => rs.map (Row.map Fin.val))

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The explicit satellite in SeedBase's earlier row conversion is the same one. -/
theorem finite_seed_satellite : ∀ r ∈ SmallSeed.allRows, r.satellite = 6 := by decide

theorem trails_length : trails.length = 6 := by
  simp only [trails, List.length_map, SmallSeed.seeds_length]

theorem trails_closed : ∀ rs ∈ trails, ClosedTrail rs := by
  intro rs hrs
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrs
  exact closedTrail_map Fin.val (SmallSeed.seeds_closed old hold)

theorem trails_row_counts : ∀ rs ∈ trails, rs.length = 16 := by
  intro rs hrs
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrs
  simpa only [List.length_map] using SmallSeed.seeds_row_counts old hold

theorem trails_charges : ∀ rs ∈ trails, (rs.map Row.charge).sum = 8 := by
  intro rs hrs
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrs
  simpa only [List.map_map, Function.comp_def, Row.map_charge] using SmallSeed.seeds_charges old hold

/-- Exact data equality connects closed trails to the existing accounting base. -/
theorem trails_flatten_eq_seedRowsNat :
    trails.flatten = Partition.SeedBase.seedRowsNat := by
  unfold trails
  rw [← List.map_flatten]
  change SmallSeed.allRows.map (Row.map Fin.val) =
    SmallSeed.allRows.map (fun r => ⟨r.base.map Fin.val, 6, r.visible⟩)
  apply List.map_congr_left
  intro r hr
  change (⟨r.base.map Fin.val, r.satellite.val, r.visible⟩ : Row Nat) =
    ⟨r.base.map Fin.val, 6, r.visible⟩
  rw [finite_seed_satellite r hr]
  rfl

theorem trails_flatten_length : trails.flatten.length = 96 := by
  rw [trails_flatten_eq_seedRowsNat]
  exact Partition.SeedBase.seedRowsNat_length

theorem trails_flatten_charge : (trails.flatten.map Row.charge).sum = 48 := by
  rw [trails_flatten_eq_seedRowsNat]
  exact Partition.SeedBase.seedRowsNat_charge

theorem trails_basedOn : BasedOn Partition.SeedBase.alphabet6 6 trails.flatten := by
  rw [trails_flatten_eq_seedRowsNat]
  exact Partition.SeedBase.seedRowsNat_basedOn

theorem trails_distinct : DistinctBlocks trails.flatten := by
  rw [trails_flatten_eq_seedRowsNat]
  exact Partition.SeedBase.seedRowsNat_distinct

/-- Six literal closed Nat trails, with their inherited row and charge counts. -/
theorem trails_certificate :
    trails.length = 6 ∧
    (∀ rs ∈ trails, ClosedTrail rs ∧ rs.length = 16 ∧ (rs.map Row.charge).sum = 8) ∧
    trails.flatten = Partition.SeedBase.seedRowsNat ∧
    trails.flatten.length = 96 ∧ (trails.flatten.map Row.charge).sum = 48 ∧
    BasedOn Partition.SeedBase.alphabet6 6 trails.flatten ∧
    DistinctBlocks trails.flatten := by
  refine ⟨trails_length, ?_, trails_flatten_eq_seedRowsNat, trails_flatten_length,
    trails_flatten_charge, trails_basedOn, trails_distinct⟩
  intro rs hrs
  exact ⟨trails_closed rs hrs, trails_row_counts rs hrs, trails_charges rs hrs⟩

#print axioms finite_seed_satellite
#print axioms trails_closed
#print axioms trails_flatten_eq_seedRowsNat
#print axioms trails_certificate

end SuperpermutationUpperBound.Certificates.NatSeeds
