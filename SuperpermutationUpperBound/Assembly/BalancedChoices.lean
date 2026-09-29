import SuperpermutationUpperBound.Assembly.RotationConnectors

namespace SuperpermutationUpperBound
variable {α : Type}

theorem short_prefix_of_equal_prefix {u v : List α} {h ell : Nat}
    (he : u.take h = v.take h) (hell : ell ≤ h) : u.take ell = v.take ell := by
  have hh := congrArg (List.take ell) he
  simpa only [List.take_take, Nat.min_eq_left hell] using hh

theorem short_suffix_of_equal_suffix {u v : List α} {h ell : Nat}
    (hu : h ≤ u.length) (hv : h ≤ v.length)
    (he : u.drop (u.length - h) = v.drop (v.length - h)) (hell : ell ≤ h) :
    u.drop (u.length - ell) = v.drop (v.length - ell) := by
  have hh := congrArg (List.drop (h - ell)) he
  rw [List.drop_drop, List.drop_drop] at hh
  simpa only [show u.length - h + (h - ell) = u.length - ell by omega,
    show v.length - h + (h - ell) = v.length - ell by omega] using hh

/-- Any family of cut words with the prescribed rotation endpoints has
balanced short endpoints, regardless of its internal macro-edge traversal. -/
theorem balanced_choices_of_rotation_endpoints (x : List α) (words : Nat → List α)
    (hx : 0 < x.length)
    (hlen : ∀ j, j < x.length → x.length ≤ (words j).length)
    (hprefix : ∀ j, j < x.length → (words j).take x.length = rot x (j + 1))
    (hsuffix : ∀ j, j < x.length →
      (words j).drop ((words j).length - x.length) = rot x j)
    (ell : Nat) (hell : ell ≤ x.length) :
    ((List.range x.length).map (fun j => (words j).take ell)).Perm
      ((List.range x.length).map (fun j => (words j).drop ((words j).length - ell))) := by
  have hp : (List.range x.length).map (fun j => (words j).take ell) =
      (List.range x.length).map (fun j => (rotationCutWord x j).take ell) := by
    apply List.map_congr_left
    intro j hj
    apply short_prefix_of_equal_prefix (h := x.length) _ hell
    rw [hprefix j (List.mem_range.mp hj), rotationCutWord_prefix]
  have hs : (List.range x.length).map (fun j => (words j).drop ((words j).length - ell)) =
      (List.range x.length).map (fun j =>
        (rotationCutWord x j).drop ((rotationCutWord x j).length - ell)) := by
    apply List.map_congr_left
    intro j hj
    apply short_suffix_of_equal_suffix (h := x.length) (hlen j (List.mem_range.mp hj))
      (by rw [rotationCutWord_length]; omega) _ hell
    rw [hsuffix j (List.mem_range.mp hj), rotationCutWord_suffix x j hx]
  rw [hp, hs]
  exact rotationCutWord_balanced x ell hx hell

end SuperpermutationUpperBound
