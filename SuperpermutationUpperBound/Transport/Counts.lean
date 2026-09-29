import SuperpermutationUpperBound.Transport.Local

/-! All-size scalar transport on labeled row occurrences. This is the exact
counting part of transport; closed trail assembly and block completeness are
separate properties and are not hypotheses hidden in these counts. -/
namespace SuperpermutationUpperBound.Transport

variable {α : Type}

def Ready (z : α) (r : Row α) : Prop :=
  r.Valid ∧ z ∉ r.base ∧ z ≠ r.satellite ∧
    (r.visible = r.base.length ∨ r.visible = r.base.length - 2)

def packingRows (rs : List (Row α)) (z : α) : List (Row α) :=
  rs.flatMap (fun r => rows r z)

theorem rows_visible_succ {r t : Row α} {z : α} (hr : Ready z r)
    (ht : t ∈ rows r z) : t.visible = r.visible + 1 := by
  have hs := (rows_local_certificate hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).2.1 t ht
  have hv := hr.1.2.2.2
  have hv' := hs.1.2.2.2
  have hc := hs.2.2
  unfold Row.charge at hc
  omega

theorem rows_visible_sum {r : Row α} {z : α} (hr : Ready z r) :
    ((rows r z).map Row.visible).sum = r.base.length * (r.visible + 1) := by
  have hlen := (rows_local_certificate hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).1
  have hconst : ∀ t ∈ rows r z, t.visible = r.visible + 1 :=
    fun _ ht => rows_visible_succ hr ht
  have hsum : ∀ ts : List (Row α), (∀ t ∈ ts, t.visible = r.visible + 1) →
      (ts.map Row.visible).sum = ts.length * (r.visible + 1) := by
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
      intro hh
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [hh t (by simp), ih (fun q hq => hh q (List.mem_cons_of_mem _ hq)), Nat.succ_mul]
      omega
  rw [hsum _ hconst, hlen]

theorem packingRows_length (rs : List (Row α)) (z : α) (n : Nat)
    (hr : ∀ r ∈ rs, Ready z r ∧ r.base.length = n) :
    (packingRows rs z).length = n * rs.length := by
  induction rs with
  | nil => simp [packingRows]
  | cons r rs ih =>
    have h := hr r (by simp)
    have hs := rows_local_certificate h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2
    have ht := ih (fun t ht => hr t (List.mem_cons_of_mem _ ht))
    change (rows r z ++ packingRows rs z).length = _
    rw [List.length_append, hs.1, h.2, ht, List.length_cons, Nat.mul_succ]
    omega

theorem packingRows_charge_sum (rs : List (Row α)) (z : α) (n : Nat)
    (hr : ∀ r ∈ rs, Ready z r ∧ r.base.length = n) :
    ((packingRows rs z).map Row.charge).sum = n * (rs.map Row.charge).sum := by
  induction rs with
  | nil => simp [packingRows]
  | cons r rs ih =>
    have h := hr r (by simp)
    have hs := rows_local_certificate h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2
    have ht := ih (fun t ht => hr t (List.mem_cons_of_mem _ ht))
    change ((rows r z ++ packingRows rs z).map Row.charge).sum = _
    rw [List.map_append, List.sum_append, hs.2.2, h.2, ht]
    simp [Nat.mul_add]

theorem packingRows_visible_sum (rs : List (Row α)) (z : α) (n : Nat)
    (hr : ∀ r ∈ rs, Ready z r ∧ r.base.length = n) :
    ((packingRows rs z).map Row.visible).sum =
      n * ((rs.map Row.visible).sum + rs.length) := by
  induction rs with
  | nil => simp [packingRows]
  | cons r rs ih =>
    have h := hr r (by simp)
    have ht := ih (fun t ht => hr t (List.mem_cons_of_mem _ ht))
    change ((rows r z ++ packingRows rs z).map Row.visible).sum = _
    rw [List.map_append, List.sum_append, rows_visible_sum h.1, h.2, ht]
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem packingRows_valid {rs : List (Row α)} {z : α} {n : Nat}
    (hr : ∀ r ∈ rs, Ready z r ∧ r.base.length = n) :
    ∀ t ∈ packingRows rs z, t.Valid ∧ t.base.length = n + 1 ∧
      (t.visible = t.base.length ∨ t.visible = t.base.length - 2) := by
  intro t ht
  obtain ⟨r, hmem, ht⟩ := List.mem_flatMap.mp ht
  have h := hr r hmem
  have hs := (rows_local_certificate h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2).2.1 t ht
  refine ⟨hs.1, by omega, ?_⟩
  have hv := rows_visible_succ h.1 ht
  have hn := h.1.1.2.2.1
  rcases h.1.2.2.2 with hf | hs'
  · left; omega
  · right; omega

/-- Exact global row, charge and visible-length recurrences, for every size. -/
theorem packingRows_counts (rs : List (Row α)) (z : α) (n : Nat)
    (hr : ∀ r ∈ rs, Ready z r ∧ r.base.length = n) :
    (packingRows rs z).length = n * rs.length ∧
    ((packingRows rs z).map Row.charge).sum = n * (rs.map Row.charge).sum ∧
    ((packingRows rs z).map Row.visible).sum =
      n * ((rs.map Row.visible).sum + rs.length) ∧
    (∀ t ∈ packingRows rs z, t.Valid ∧ t.base.length = n + 1 ∧
      (t.visible = t.base.length ∨ t.visible = t.base.length - 2)) :=
  ⟨packingRows_length rs z n hr, packingRows_charge_sum rs z n hr,
    packingRows_visible_sum rs z n hr, packingRows_valid hr⟩

end SuperpermutationUpperBound.Transport
