import SuperpermutationUpperBound43.Certificate.BaseFacts
import SuperpermutationUpperBound43.Certificate.CirclesData

namespace SuperpermutationUpperBound43.Certificate.Circles
open SuperpermutationUpperBound SuperpermutationUpperBound.CircleTransport
open SuperpermutationUpperBound.Certificates.CircleBase

set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

theorem circles_count : circles.length = 357 := by decide
theorem circles_valid : CircleFamilyValid 8 circles := by
  unfold CircleFamilyValid
  decide
theorem circles_avoid_satellite : ∀ c ∈ circles, 9 ∉ c := by decide
theorem circles_support : ∀ c ∈ circles, ∀ a ∈ c, a < 11 := by decide
theorem mixedPointers_count : mixedPointers.length = 1792 := by decide
theorem ordinaryPointers_count : ordinaryPointers.length = 126 := by decide

theorem mixed_valid : ∀ p ∈ mixedPointers, p.Valid components circles 10 8 := by
  unfold MixedPointer.Valid
  simp only [components_count, circles_count]
  decide

theorem ordinary_valid : ∀ p ∈ ordinaryPointers, p.Valid components circles 9 := by
  unfold OrdinaryPointer.Valid
  simp only [components_count, circles_count]
  decide

theorem mixed_labels_exact :
    mixedPointers.map (fun p => (p.component, p.port)) =
      mixedComponents.flatMap (fun i => (List.range 8).map (fun j => (i,j))) := by decide

theorem component_labels_cover : ∀ i : Fin 350,
    i.val ∈ mixedComponents ∨ i.val ∈ ordinaryPointers.map OrdinaryPointer.component := by decide

theorem pointers_cover : ∀ i : Fin 350, ∀ j : Fin 8,
    (∃ p ∈ mixedPointers, p.component = i.val ∧ p.port = j.val) ∨
      (∃ p ∈ ordinaryPointers, p.component = i.val) := by
  intro i j
  rcases component_labels_cover i with hm | ho
  · have hl : (i.val, j.val) ∈ mixedPointers.map (fun p => (p.component, p.port)) := by
      rw [mixed_labels_exact]
      exact List.mem_flatMap.mpr ⟨i.val, hm,
        List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩⟩
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hl
    exact Or.inl ⟨p, hp, congrArg Prod.fst he, congrArg Prod.snd he⟩
  · obtain ⟨p, hp, he⟩ := List.mem_map.mp ho
    exact Or.inr ⟨p, hp, he⟩

theorem safe_cover : SafeCircleCover family 10 8 circles := by
  have hh := pointers_safe_cover components circles 10 9 8 (by decide)
    mixedPointers ordinaryPointers
    (fun rs hrs r hr => (components_shape rs hrs r hr).1)
    (fun rs hrs r hr => (components_shape rs hrs r hr).2.2)
    mixed_valid ordinary_valid
    (fun i j => pointers_cover ⟨i.val, by simpa only [components_count] using i.isLt⟩ j)
  intro i j
  exact hh ⟨i.val, by simpa only [components_count] using i.isLt⟩ j

end SuperpermutationUpperBound43.Certificate.Circles
