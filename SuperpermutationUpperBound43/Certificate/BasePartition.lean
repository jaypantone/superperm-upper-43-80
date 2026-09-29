import SuperpermutationUpperBound43.Certificate.Inventory.Result

/-! Staged kernel checks prove uniqueness of the canonical row bases.
Generic membership and cardinality recover the complete reference inventory. -/
namespace SuperpermutationUpperBound43.Certificate
open SuperpermutationUpperBound

theorem canonical_inventory :
    (rows.map (fun r => canonical r.base)).Perm canonicalBases :=
  Inventory.inventory_of_nodup rows_basedOn Inventory.Result.normalized_rows_nodup rows_count

theorem rows_complete : BlockComplete Partition.SprintBase.alphabet9 rows :=
  complete_of_canonical_inventory rows_basedOn canonical_inventory

theorem rows_distinct : DistinctBlocks rows :=
  distinct_of_canonical_inventory rows_basedOn canonical_inventory

end SuperpermutationUpperBound43.Certificate
