import SuperpermutationUpperBound.Certificates.CircleBaseFacts

namespace SuperpermutationUpperBound.Certificates.Circle54
open CircleBase CircleTransport


def circles : List (List Nat) := [
  [1,7,9,2,3,5,6],
  [1,7,2,3,9,5,6],
  [1,7,2,3,5,9,6],
  [0,6,1,9,5,7,3],
  [0,6,1,5,9,7,3],
  [0,6,1,5,7,3,9],
  [0,1,3,2,4,5,6],
  [0,1,3,6,5,2,4],
  [0,1,4,2,3,6,5],
  [0,1,4,5,6,2,3],
  [0,1,5,2,6,3,4],
  [0,1,5,4,3,2,6],
  [0,1,6,2,5,4,3],
  [0,1,6,3,4,2,5],
  [0,2,3,1,5,4,6],
  [0,2,3,6,4,1,5],
  [0,2,4,1,6,3,5],
  [0,2,4,5,3,1,6],
  [0,2,5,1,3,6,4],
  [0,2,5,4,6,1,3],
  [0,2,6,1,4,5,3],
  [0,2,6,3,5,1,4],
  [0,3,1,2,5,6,4],
  [0,3,1,6,4,5,2],
  [0,3,2,1,4,6,5],
  [0,3,2,6,5,4,1],
  [0,3,4,5,2,6,1],
  [0,3,4,6,1,2,5],
  [0,3,5,4,1,6,2],
  [0,3,5,6,2,1,4],
  [0,4,1,2,6,5,3],
  [0,4,1,5,3,6,2],
  [0,4,2,1,3,5,6],
  [0,4,2,5,6,3,1],
  [0,4,3,5,1,2,6],
  [0,4,3,6,2,5,1],
  [0,4,6,3,1,5,2],
  [0,4,6,5,2,1,3],
  [0,5,1,2,3,4,6],
  [0,5,1,4,6,3,2],
  [0,5,2,1,6,4,3],
  [0,5,2,4,3,6,1],
  [0,5,3,4,2,1,6],
  [0,5,3,6,1,4,2],
  [0,5,6,3,2,4,1],
  [0,5,6,4,1,2,3],
  [0,6,1,2,4,3,5],
  [0,6,1,3,5,4,2],
  [0,6,2,1,5,3,4],
  [0,6,2,3,4,5,1],
  [0,6,4,3,2,1,5],
  [0,6,4,5,1,3,2],
  [0,6,5,3,1,2,4],
  [0,6,5,4,2,3,1]]

def mixedPointers : List MixedPointer := [
  ⟨0,0,4,1953,1,3⟩,
  ⟨0,1,0,1320,2,0⟩,
  ⟨0,2,5,1953,3,3⟩,
  ⟨0,3,1,1320,4,0⟩,
  ⟨0,4,2,1320,5,0⟩,
  ⟨0,5,3,1953,6,4⟩,
  ⟨0,6,3,1953,0,3⟩,
  ⟨1,0,3,528,3,0⟩,
  ⟨1,1,4,528,4,0⟩,
  ⟨1,2,0,1701,5,4⟩,
  ⟨1,3,5,528,6,0⟩,
  ⟨1,4,5,528,0,6⟩,
  ⟨1,5,1,1701,1,3⟩,
  ⟨1,6,2,1701,2,3⟩,
  ⟨2,0,4,67,0,4⟩,
  ⟨2,1,0,54,1,1⟩,
  ⟨2,2,5,67,2,4⟩,
  ⟨2,3,1,54,3,1⟩,
  ⟨2,4,2,54,4,1⟩,
  ⟨2,5,3,67,5,5⟩,
  ⟨2,6,4,67,6,5⟩,
  ⟨3,0,3,295,4,6⟩,
  ⟨3,1,4,295,5,6⟩,
  ⟨3,2,0,282,6,3⟩,
  ⟨3,3,0,282,0,2⟩,
  ⟨3,4,5,295,1,5⟩,
  ⟨3,5,1,282,2,2⟩,
  ⟨3,6,2,282,3,2⟩]

def ordinaryPointers : List OrdinaryPointer := [
  ⟨4,6,0,[0,1,3,2,4,5,6],7⟩,
  ⟨5,7,0,[0,1,3,6,5,2,4],7⟩,
  ⟨6,8,0,[0,1,4,2,3,6,5],7⟩,
  ⟨7,9,0,[0,1,4,5,6,2,3],7⟩,
  ⟨8,10,0,[0,1,5,2,6,3,4],7⟩,
  ⟨9,11,0,[0,1,5,4,3,2,6],7⟩,
  ⟨10,12,0,[0,1,6,2,5,4,3],7⟩,
  ⟨11,13,0,[0,1,6,3,4,2,5],7⟩,
  ⟨12,14,0,[0,2,3,1,5,4,6],7⟩,
  ⟨13,15,0,[0,2,3,6,4,1,5],7⟩,
  ⟨14,16,0,[0,2,4,1,6,3,5],7⟩,
  ⟨15,17,0,[0,2,4,5,3,1,6],7⟩,
  ⟨16,18,0,[0,2,5,1,3,6,4],7⟩,
  ⟨17,19,0,[0,2,5,4,6,1,3],7⟩,
  ⟨18,20,0,[0,2,6,1,4,5,3],7⟩,
  ⟨19,21,0,[0,2,6,3,5,1,4],7⟩,
  ⟨20,22,0,[0,3,1,2,5,6,4],7⟩,
  ⟨21,23,0,[0,3,1,6,4,5,2],7⟩,
  ⟨22,24,0,[0,3,2,1,4,6,5],7⟩,
  ⟨23,25,0,[0,3,2,6,5,4,1],7⟩,
  ⟨24,26,0,[0,3,4,5,2,6,1],7⟩,
  ⟨25,27,0,[0,3,4,6,1,2,5],7⟩,
  ⟨26,28,0,[0,3,5,4,1,6,2],7⟩,
  ⟨27,29,0,[0,3,5,6,2,1,4],7⟩,
  ⟨28,30,0,[0,4,1,2,6,5,3],7⟩,
  ⟨29,31,0,[0,4,1,5,3,6,2],7⟩,
  ⟨30,32,0,[0,4,2,1,3,5,6],7⟩,
  ⟨31,33,0,[0,4,2,5,6,3,1],7⟩,
  ⟨32,34,0,[0,4,3,5,1,2,6],7⟩,
  ⟨33,35,0,[0,4,3,6,2,5,1],7⟩,
  ⟨34,36,0,[0,4,6,3,1,5,2],7⟩,
  ⟨35,37,0,[0,4,6,5,2,1,3],7⟩,
  ⟨36,38,0,[0,5,1,2,3,4,6],7⟩,
  ⟨37,39,0,[0,5,1,4,6,3,2],7⟩,
  ⟨38,40,0,[0,5,2,1,6,4,3],7⟩,
  ⟨39,41,0,[0,5,2,4,3,6,1],7⟩,
  ⟨40,42,0,[0,5,3,4,2,1,6],7⟩,
  ⟨41,43,0,[0,5,3,6,1,4,2],7⟩,
  ⟨42,44,0,[0,5,6,3,2,4,1],7⟩,
  ⟨43,45,0,[0,5,6,4,1,2,3],7⟩,
  ⟨44,46,0,[0,6,1,2,4,3,5],7⟩,
  ⟨45,47,0,[0,6,1,3,5,4,2],7⟩,
  ⟨46,48,0,[0,6,2,1,5,3,4],7⟩,
  ⟨47,49,0,[0,6,2,3,4,5,1],7⟩,
  ⟨48,50,0,[0,6,4,3,2,1,5],7⟩,
  ⟨49,51,0,[0,6,4,5,1,3,2],7⟩,
  ⟨50,52,0,[0,6,5,3,1,2,4],7⟩,
  ⟨51,53,0,[0,6,5,4,2,3,1],7⟩]

set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

theorem circles_count : circles.length = 54 := by decide
theorem circles_valid : CircleFamilyValid 7 circles := by unfold CircleFamilyValid; decide
theorem circles_avoid_satellite : ∀ c ∈ circles, 8 ∉ c := by decide
theorem circles_support : ∀ c ∈ circles, ∀ a ∈ c, a < 10 := by decide

theorem mixed_valid : ∀ p ∈ mixedPointers, p.Valid (components8 8) circles 9 7 := by
  unfold MixedPointer.Valid
  simp only [components8_count, components9_count, circles_count]
  decide
theorem ordinary_valid : ∀ p ∈ ordinaryPointers, p.Valid (components8 8) circles 8 := by
  unfold OrdinaryPointer.Valid
  simp only [components8_count, components9_count, circles_count]
  decide
theorem pointers_cover : ∀ i : Fin 52, ∀ j : Fin 7,
    (∃ p ∈ mixedPointers, p.component = i.val ∧ p.port = j.val) ∨
      (∃ p ∈ ordinaryPointers, p.component = i.val) := by decide

theorem safe_cover : SafeCircleCover family8 9 7 circles := by
  have hh := pointers_safe_cover (components8 8) circles 9 8 7 (by decide)
    mixedPointers ordinaryPointers
    (fun rs hrs r hr => (components8_shape 8 rs hrs r hr).1)
    (fun rs hrs r hr => (components8_shape 8 rs hrs r hr).2.2)
    mixed_valid ordinary_valid
    (fun i j => pointers_cover ⟨i.val, by simpa only [components8_count, components9_count] using i.isLt⟩ j)
  intro i j
  exact hh ⟨i.val, by simpa only [components8_count, components9_count] using i.isLt⟩ j

end SuperpermutationUpperBound.Certificates.Circle54
