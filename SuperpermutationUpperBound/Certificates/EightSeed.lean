import SuperpermutationUpperBound.Certificates.SmallSeed
import SuperpermutationUpperBound.Foundation.RowRelabeling
import SuperpermutationUpperBound.Partition.SeedBase
import SuperpermutationUpperBound.Transport.Successor
import SuperpermutationUpperBound.Transport.OrbitAssembly

/-! A compact 120-row seed for the eight-symbol construction.
Only its 60-digit deficit pattern is construction input; the literal walk
and its semantic row and block properties are checked in the kernel. -/
namespace SuperpermutationUpperBound.Certificates.EightSeed

open Partition Partition.SeedBase

def pattern : List Nat :=
  [2,0,0,0,2,0,0,0,2,0,0,2,0,0,0,2,0,2,2,2,0,0,0,2,0,0,2,0,0,0,
   2,0,2,2,2,0,0,2,0,0,0,2,2,2,0,2,0,0,0,2,0,0,2,0,0,0,2,2,2,0]

def seed : List (Row Nat) :=
  (SmallSeed.walk [0,1,2,3,4,5] (pattern ++ pattern)).map (Row.map Fin.val)

set_option maxRecDepth 40000
set_option maxHeartbeats 12000000

theorem seed_length : seed.length = 120 := by decide

theorem seed_charge : (seed.map Row.charge).sum = 96 := by decide

theorem seed_visible : (seed.map Row.visible).sum = 624 := by decide

theorem seed_basedOn : BasedOn alphabet6 6 seed := by
  unfold BasedOn
  decide

theorem seed_closed : ClosedTrail seed := by
  unfold ClosedTrail CyclicallyCompatible Row.Compatible
  decide

theorem seed_distinct : DistinctBlocks seed := by
  unfold DistinctBlocks
  decide

/-- The finite check uses the same semantic cyclic relation as BlockComplete. -/
theorem seed_canonical_complete : ∀ b ∈ canonicalBases6, ∃ r ∈ seed, CyclicEq r.base b := by
  have hc : ∀ b ∈ (List.permutations' [1,2,3,4,5]).map (fun t : List Nat => 0 :: t),
      ∃ r ∈ seed, CyclicEq r.base b := by decide
  have hp := (List.permutations_perm_permutations' ([1,2,3,4,5] : List Nat)).map
    (fun t => 0 :: t)
  intro b hb
  exact hc b (hp.mem_iff.mp hb)

theorem seed_complete : BlockComplete alphabet6 seed := by
  intro x hx
  obtain ⟨b, hb, hbx⟩ := canonicalBases6_complete hx
  obtain ⟨r, hr, hrb⟩ := seed_canonical_complete b hb
  exact ⟨r, hr, hrb.trans hbx⟩

theorem seed_certificate : seed.length = 120 ∧ (seed.map Row.charge).sum = 96 ∧
    BasedOn alphabet6 6 seed ∧ ClosedTrail seed ∧ DistinctBlocks seed ∧
    BlockComplete alphabet6 seed :=
  ⟨seed_length, seed_charge, seed_basedOn, seed_closed, seed_distinct, seed_complete⟩

abbrev State := Fin 120 × Fin 5

def seedRow (i : Fin 120) : Row Nat := seed[i.val]'(by rw [seed_length]; exact i.isLt)

def next (ip : State) : State :=
  (ip.1 + 1, ip.2 + if (pattern ++ pattern)[ip.1.val]?.getD 0 = 0 then 4 else 1)

def labels : List State := Transport.orbitLabels next (0,0) 600

set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

theorem next_eq : ∀ ip : State,
    next ip = Transport.rowPortSuccessor (by decide : 0 < 120) 6 (by decide) seedRow ip := by
  intro ip
  rcases ip with ⟨i,p⟩
  revert p i
  decide

theorem orbit_return : Transport.advance next (0,0) 600 = (0,0) := by decide

theorem labels_inventory : labels.Perm ((List.finRange 120).product (List.finRange 5)) := by
  decide

#print axioms next_eq
#print axioms orbit_return
#print axioms labels_inventory
#print axioms seed_certificate
#print axioms seed_canonical_complete

end SuperpermutationUpperBound.Certificates.EightSeed
