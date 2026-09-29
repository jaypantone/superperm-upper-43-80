import SuperpermutationUpperBound.Partition.SprintBase
import SuperpermutationUpperBound.CircleTransport.TrackCounts
import SuperpermutationUpperBound.Certificates.CirclePointers

/-! The exact source components of the earlier construction, used by both
finite circle covers. Component labels follow the transport order. -/
namespace SuperpermutationUpperBound.Certificates.CircleBase

open CircleTransport Transport

def retag (satellite : Nat) (r : Row Nat) : Row Nat :=
  ⟨r.base, satellite, r.visible⟩

def seedA9 : List (Row Nat) := NineRecipe.seedA.map (retag 9)
def seedB9 : List (Row Nat) := NineRecipe.seedB.map (retag 9)

/-- The two returning port orbits for each seed have the orders shown here.
Their shifts differ: -290 is 4 modulo 6, while -46 is 2 modulo 6. -/
def mixed8 : List (List (Row Nat)) :=
  [([0,4,2] : List Nat).flatMap (transportWalk seedA9 7),
   ([1,5,3] : List Nat).flatMap (transportWalk seedA9 7),
   ([0,2,4] : List Nat).flatMap (transportWalk seedB9 7),
   ([1,3,5] : List Nat).flatMap (transportWalk seedB9 7)]

def rawComponents8 : List (List (Row Nat)) :=
  mixed8 ++ NineRecipe.unusedBases.map (fun x => Partition.fullChart x 7 9)

/-- Parameterizing the source satellite lets the same labelled bases serve
the 54-cover (satellite 8, final 9) and the 377-cover (satellite 9, final 10). -/
def components8 (satellite : Nat) : List (List (Row Nat)) :=
  rawComponents8.map (List.map (retag satellite))

/-- At the second transport all seven ports return individually. Component
`7*i+j` is the track beginning at port `j` in old component `i`. -/
def components9 : List (List (Row Nat)) :=
  (components8 9).flatMap (fun rs => (List.range 7).map (transportWalk rs 8))

theorem components8_count (satellite : Nat) : (components8 satellite).length = 52 := by
  simp [components8, rawComponents8, mixed8, NineRecipe.unusedBases_length]

theorem components9_count : components9.length = 364 := by
  simp [components9, List.length_flatMap, components8_count]

set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

theorem rawComponents8_shape : ∀ rs ∈ rawComponents8, ∀ r ∈ rs,
    r.base.length = 8 ∧ r.satellite = 9 ∧
      (r.visible = r.base.length ∨ r.visible = r.base.length - 2) := by decide

theorem rawComponents8_closed : ∀ rs ∈ rawComponents8, ClosedTrail rs := by
  unfold ClosedTrail CyclicallyCompatible Row.Compatible
  decide

theorem rawComponents8_winding : ∀ rs ∈ rawComponents8, (7 : Int) ∣ signedExcess rs := by decide

theorem rawComponents8_inventory_sorted :
    NineRecipe.sortFuel NineRecipe.rowLE 13 rawComponents8.flatten =
      NineRecipe.sortFuel NineRecipe.rowLE 13 Partition.SprintBase.rows8 := by decide

theorem rawComponents8_inventory : rawComponents8.flatten.Perm Partition.SprintBase.rows8 :=
  (NineRecipe.sortFuel_perm NineRecipe.rowLE 13 rawComponents8.flatten).symm.trans
    ((List.Perm.of_eq rawComponents8_inventory_sorted).trans
      (NineRecipe.sortFuel_perm NineRecipe.rowLE 13 Partition.SprintBase.rows8))

def family8 (i : Fin 52) : List (Row Nat) := componentAt (components8 8) i.val
def family9 (i : Fin 364) : List (Row Nat) := componentAt components9 i.val

end SuperpermutationUpperBound.Certificates.CircleBase
