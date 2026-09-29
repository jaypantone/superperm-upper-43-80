import SuperpermutationUpperBound.Transport.Ports
import SuperpermutationUpperBound.TrailSpelling

/-! Exhaustive local port paths retain every replacement row occurrence. -/
namespace SuperpermutationUpperBound.Transport

variable {α : Type}

def fullAt (r : Row α) (z : α) (j : Nat) : Row α :=
  ⟨insertLetter r.base z j, r.satellite, r.base.length + 1⟩

def shortAt (r : Row α) (z : α) (j : Nat) : Row α :=
  ⟨insertLetter r.base z j, r.satellite, r.base.length - 1⟩

def shortLast (r : Row α) (z : α) : Row α :=
  ⟨rot r.base (r.base.length - 1) ++ [z], r.satellite, r.base.length - 1⟩

def fullPaths (r : Row α) (z : α) : List (List (Row α)) :=
  [[fullAt r z 0, fullAt r z (r.base.length - 1)]] ++
    (List.range' 1 (r.base.length - 2)).map (fun j => [fullAt r z j])

def shortPaths (r : Row α) (z : α) : List (List (Row α)) :=
  (List.range (r.base.length - 2)).map (fun j => [shortAt r z j]) ++
    [[shortAt r z (r.base.length - 2), shortLast r z]]

theorem fullRows_eq_map (r : Row α) (z : α) :
    fullRows r z = (List.range r.base.length).map (fullAt r z) := by
  simp only [fullRows, fullBases, List.map_map]
  rfl

theorem shortRows_eq_map (r : Row α) (z : α) :
    shortRows r z = (List.range (r.base.length - 1)).map (shortAt r z) ++ [shortLast r z] := by
  simp only [shortRows, shortBases, List.map_append, List.map_map,
    List.map_cons, List.map_nil]
  rfl

theorem flatten_map_singletons (xs : List Nat) (f : Nat → Row α) :
    (xs.map (fun j => [f j])).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons, List.flatten_cons, List.singleton_append, ih]

theorem fullPaths_flatten (r : Row α) (z : α) :
    (fullPaths r z).flatten =
      fullAt r z 0 :: fullAt r z (r.base.length - 1) ::
        (List.range' 1 (r.base.length - 2)).map (fullAt r z) := by
  simp [fullPaths, flatten_map_singletons]

theorem shortPaths_flatten (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (shortPaths r z).flatten = shortRows r z := by
  rw [shortRows_eq_map]
  have heq : r.base.length - 1 = (r.base.length - 2) + 1 := by omega
  rw [heq, List.range_succ]
  simp [shortPaths, flatten_map_singletons, List.map_append, List.append_assoc]

theorem range_split_ends (n : Nat) (hn : 2 ≤ n) :
    List.range n = 0 :: (List.range' 1 (n - 2) ++ [n - 1]) := by
  have hn' : n = (n - 2) + 2 := by omega
  have htail : n - 1 = (n - 2) + 1 := by omega
  conv => lhs; rw [hn']
  rw [List.range_eq_range', List.range'_succ, List.range'_1_concat]
  simp only [Nat.zero_add, htail, Nat.add_comm 1 (n - 2)]

/-- Every full replacement occurrence appears exactly once in the local paths. -/
theorem fullPaths_flatten_perm (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (fullPaths r z).flatten.Perm (fullRows r z) := by
  rw [fullPaths_flatten, fullRows_eq_map, range_split_ends r.base.length hn]
  simp only [List.map_cons, List.map_append]
  exact (List.perm_append_singleton (fullAt r z (r.base.length - 1))
    ((List.range' 1 (r.base.length - 2)).map (fullAt r z))).symm.cons _

theorem fullPaths_nonempty {r : Row α} {z : α} {path : List (Row α)}
    (hp : path ∈ fullPaths r z) : path ≠ [] := by
  simp only [fullPaths, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨j, _, rfl⟩ <;> simp

theorem shortPaths_nonempty {r : Row α} {z : α} {path : List (Row α)}
    (hp : path ∈ shortPaths r z) : path ≠ [] := by
  simp only [shortPaths, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with ⟨j, _, rfl⟩ | rfl <;> simp

theorem exists_append_last (x : List α) (hx : 1 ≤ x.length) :
    ∃ u b, x = u ++ [b] := by
  have hne : x ≠ [] := by intro h; simp [h] at hx
  exact ⟨x.dropLast, x.getLast hne, (List.dropLast_concat_getLast hne).symm⟩

theorem exists_cons_append_last (x : List α) (hx : 2 ≤ x.length) :
    ∃ a u b, x = a :: (u ++ [b]) := by
  obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < x.length)
  obtain ⟨u, b, rfl⟩ := exists_append_last tail (by simp only [List.length_cons] at hx; omega)
  exact ⟨a, u, b, rfl⟩

theorem exists_append_two (x : List α) (hx : 2 ≤ x.length) :
    ∃ u p b, x = u ++ [p, b] := by
  obtain ⟨v, b, rfl⟩ := exists_append_last x (by omega)
  obtain ⟨u, p, rfl⟩ := exists_append_last v (by
    simp only [List.length_append, List.length_singleton] at hx; omega)
  exact ⟨u, p, b, by simp⟩

theorem fullAt_exceptional_compatible (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (fullAt r z 0).Compatible (fullAt r z (r.base.length - 1)) := by
  obtain ⟨a, u, b, hx⟩ := exists_cons_append_last r.base hn
  have h0 : fullAt r z 0 = Row.mk (z :: a :: (u ++ [b])) r.satellite (u.length + 3) := by
    simp [fullAt, hx, insertLetter]
  have hlast : fullAt r z (r.base.length - 1) =
      Row.mk (a :: (u ++ [z, b])) r.satellite (u.length + 3) := by
    simp only [fullAt, hx]
    have hlen : (a :: (u ++ [b])).length = u.length + 2 := by simp
    rw [hlen]
    have hsub : u.length + 2 - 1 = u.length + 1 := by omega
    rw [hsub, full_final_base]
  rw [h0, hlast]
  exact full_exceptional_compatible a u z b r.satellite

theorem shortAt_exceptional_compatible (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (shortAt r z (r.base.length - 2)).Compatible (shortLast r z) := by
  obtain ⟨u, p, b, hx⟩ := exists_append_two r.base hn
  have hfirst : shortAt r z (r.base.length - 2) =
      Row.mk (u ++ [z, p, b]) r.satellite (u.length + 1) := by
    simp [shortAt, hx, short_exceptional_first_base]
  have hlast : shortLast r z = Row.mk (b :: (u ++ [p, z])) r.satellite (u.length + 1) := by
    simp [shortLast, hx, short_exceptional_second_base]
  rw [hfirst, hlast]
  exact short_exceptional_compatible u z p b r.satellite

theorem fullPaths_compatible {r : Row α} {z : α} (hn : 2 ≤ r.base.length)
    {first : Row α} {rest : List (Row α)} (hp : first :: rest ∈ fullPaths r z) :
    RowTrailCompatible first rest := by
  simp only [fullPaths, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with h | ⟨j, _, h⟩
  · cases h
    exact ⟨fullAt_exceptional_compatible r z hn, True.intro⟩
  · cases h
    exact True.intro

theorem shortPaths_compatible {r : Row α} {z : α} (hn : 2 ≤ r.base.length)
    {first : Row α} {rest : List (Row α)} (hp : first :: rest ∈ shortPaths r z) :
    RowTrailCompatible first rest := by
  simp only [shortPaths, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with ⟨j, _, h⟩ | h
  · cases h
    exact True.intro
  · cases h
    exact ⟨shortAt_exceptional_compatible r z hn, True.intro⟩

theorem fullPaths_length (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (fullPaths r z).length = r.base.length - 1 := by
  simp only [fullPaths, List.length_append, List.length_singleton,
    List.length_map, List.length_range']
  omega

theorem shortPaths_length (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (shortPaths r z).length = r.base.length - 1 := by
  simp only [shortPaths, List.length_append, List.length_singleton,
    List.length_map, List.length_range]
  omega

/-- Full local path splitting is an exhaustive occurrence partition. -/
theorem fullPaths_certificate (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (fullPaths r z).length = r.base.length - 1 ∧
      (fullPaths r z).flatten.Perm (fullRows r z) ∧
      ∀ path ∈ fullPaths r z, ∃ first rest,
        path = first :: rest ∧ RowTrailCompatible first rest := by
  refine ⟨fullPaths_length r z hn, fullPaths_flatten_perm r z hn, ?_⟩
  intro path hp
  obtain ⟨first, rest, heq⟩ := List.exists_cons_of_ne_nil (fullPaths_nonempty hp)
  exact ⟨first, rest, heq, fullPaths_compatible hn (heq ▸ hp)⟩

/-- Short local path splitting is exhaustive even in its original occurrence order. -/
theorem shortPaths_certificate (r : Row α) (z : α) (hn : 2 ≤ r.base.length) :
    (shortPaths r z).length = r.base.length - 1 ∧
      (shortPaths r z).flatten = shortRows r z ∧
      ∀ path ∈ shortPaths r z, ∃ first rest,
        path = first :: rest ∧ RowTrailCompatible first rest := by
  refine ⟨shortPaths_length r z hn, shortPaths_flatten r z hn, ?_⟩
  intro path hp
  obtain ⟨first, rest, heq⟩ := List.exists_cons_of_ne_nil (shortPaths_nonempty hp)
  exact ⟨first, rest, heq, shortPaths_compatible hn (heq ▸ hp)⟩

theorem fullAt_singleton_endpoints (r : Row α) (z : α) (j : Nat)
    (hn : 2 ≤ r.base.length) (hfull : r.visible = r.base.length)
    (hjlo : 1 ≤ j) (hjhi : j ≤ r.base.length - 2) :
    (fullAt r z j).head = insertLetter r.head z j ∧
      (fullAt r z j).tail = insertLetter r.tail z (j - 1) := by
  have hr : Row.mk r.base r.satellite r.base.length = r := by cases r; simp_all
  constructor
  · simpa only [fullAt, hr] using full_insert_head r.base z r.satellite j hn hjhi
  · simpa only [fullAt, hr] using full_singleton_tail r.base z r.satellite j hn hjlo hjhi

theorem shortAt_singleton_endpoints (r : Row α) (z : α) (j : Nat)
    (hn : 3 ≤ r.base.length) (hshort : r.visible = r.base.length - 2)
    (hj : j < r.base.length - 2) :
    (shortAt r z j).head = insertLetter r.head z j ∧
      (shortAt r z j).tail = insertLetter r.tail z (j + 1) := by
  obtain ⟨u, p, b, hx⟩ := exists_append_two r.base (by omega)
  have hlen : r.base.length = u.length + 2 := by simp [hx]
  have hr : Row.mk (u ++ [p, b]) r.satellite u.length = r := by
    cases r
    simp_all
  have hnew : shortAt r z j =
      Row.mk (insertLetter (u ++ [p, b]) z j) r.satellite (u.length + 1) := by
    simp [shortAt, hx]
  rw [hnew]
  constructor
  · simpa only [hr] using short_singleton_head u z p b r.satellite j (by omega)
  · simpa only [hr] using short_singleton_tail u z p b r.satellite j (by omega)

theorem fullAt_exceptional_endpoints (r : Row α) (z : α)
    (hn : 2 ≤ r.base.length) (hfull : r.visible = r.base.length) :
    (fullAt r z 0).head = insertLetter r.head z 0 ∧
      (fullAt r z 0).Compatible (fullAt r z (r.base.length - 1)) ∧
      (fullAt r z (r.base.length - 1)).tail =
        insertLetter r.tail z (r.base.length - 2) := by
  obtain ⟨a, u, b, hx⟩ := exists_cons_append_last r.base hn
  have hlen : r.base.length = u.length + 2 := by simp [hx]
  have hr : Row.mk (a :: (u ++ [b])) r.satellite (u.length + 2) = r := by
    cases r
    simp_all
  have h0 : fullAt r z 0 = Row.mk (z :: a :: (u ++ [b])) r.satellite (u.length + 3) := by
    simp [fullAt, hx, insertLetter]
  have hlast : fullAt r z (r.base.length - 1) =
      Row.mk (a :: (u ++ [z, b])) r.satellite (u.length + 3) := by
    unfold fullAt
    rw [hlen]
    have hsub : u.length + 2 - 1 = u.length + 1 := by omega
    rw [hx, hsub, full_final_base]
  rw [h0, hlast]
  have h := full_exceptional_path a u z b r.satellite
  dsimp only at h
  simpa only [hr, hlen, Nat.add_sub_cancel] using h

theorem shortAt_exceptional_endpoints (r : Row α) (z : α)
    (hn : 3 ≤ r.base.length) (hshort : r.visible = r.base.length - 2) :
    (shortAt r z (r.base.length - 2)).head =
        insertLetter r.head z (r.base.length - 2) ∧
      (shortAt r z (r.base.length - 2)).Compatible (shortLast r z) ∧
      (shortLast r z).tail = insertLetter r.tail z 0 := by
  obtain ⟨u, p, b, hx⟩ := exists_append_two r.base (by omega)
  have hlen : r.base.length = u.length + 2 := by simp [hx]
  have hr : Row.mk (u ++ [p, b]) r.satellite u.length = r := by
    cases r
    simp_all
  have hfirst : shortAt r z (r.base.length - 2) =
      Row.mk (u ++ [z, p, b]) r.satellite (u.length + 1) := by
    simp [shortAt, hx, short_exceptional_first_base]
  have hlast : shortLast r z = Row.mk (b :: (u ++ [p, z])) r.satellite (u.length + 1) := by
    simp [shortLast, hx, short_exceptional_second_base]
  rw [hfirst, hlast]
  have h := short_exceptional_path u z p b r.satellite (by omega)
  dsimp only at h
  simpa only [hr, hlen, Nat.add_sub_cancel] using h

end SuperpermutationUpperBound.Transport
