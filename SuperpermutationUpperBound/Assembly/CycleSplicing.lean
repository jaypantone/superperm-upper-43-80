import SuperpermutationUpperBound.Foundation.Rotation

/-! Directed paths and cycle splicing for arbitrary edge values. Edges are
retained with their list multiplicities; no simple-graph assumption is made. -/
namespace SuperpermutationUpperBound

variable {β : Type u} {V : Type v}

inductive EdgePath (src dst : β → V) : V → List β → V → Prop
  | nil (v : V) : EdgePath src dst v [] v
  | cons {start finish : V} {e : β} {es : List β}
      (he : src e = start) (ht : EdgePath src dst (dst e) es finish) :
      EdgePath src dst start (e :: es) finish

namespace EdgePath

variable {src dst : β → V}

theorem eq_of_nil {a b : V} (h : EdgePath src dst a [] b) : a = b := by
  cases h
  rfl

theorem append {a b c : V} {xs ys : List β}
    (hx : EdgePath src dst a xs b) (hy : EdgePath src dst b ys c) :
    EdgePath src dst a (xs ++ ys) c := by
  induction hx with
  | nil => exact hy
  | cons he ht ih => exact .cons he (ih hy)

theorem append_iff {a c : V} {xs ys : List β} :
    EdgePath src dst a (xs ++ ys) c ↔
      ∃ b, EdgePath src dst a xs b ∧ EdgePath src dst b ys c := by
  constructor
  · intro h
    induction xs generalizing a with
    | nil => exact ⟨a, .nil a, h⟩
    | cons e es ih =>
      cases h with
      | cons he ht =>
        obtain ⟨b, hl, hr⟩ := ih ht
        exact ⟨b, .cons he hl, hr⟩
  · intro ⟨b, hx, hy⟩
    exact hx.append hy

theorem source_eq_of_cons {a b : V} {e : β} {es : List β}
    (h : EdgePath src dst a (e :: es) b) : src e = a := by
  cases h with
  | cons he _ => exact he

theorem tail_of_cons {a b : V} {e : β} {es : List β}
    (h : EdgePath src dst a (e :: es) b) : EdgePath src dst (dst e) es b := by
  cases h with
  | cons _ ht => exact ht

/-- Cutting a closed path and reversing the two pieces changes only its
basepoint. -/
theorem rotate_cut {a : V} {left right : List β}
    (h : EdgePath src dst a (left ++ right) a) :
    ∃ b, EdgePath src dst b (right ++ left) b := by
  obtain ⟨b, hl, hr⟩ := append_iff.mp h
  exact ⟨b, hr.append hl⟩

/-- A chosen edge occurrence can be made the first edge of a closed cycle.
The source is the actual endpoint value, even when other endpoints coincide. -/
theorem rotate_at_mem {a : V} {es : List β} (h : EdgePath src dst a es a)
    {e : β} (he : e ∈ es) :
    ∃ left right, es = left ++ e :: right ∧
      EdgePath src dst (src e) ((e :: right) ++ left) (src e) := by
  obtain ⟨left, right, rfl, _⟩ := List.eq_append_cons_of_mem he
  obtain ⟨b, hl, hr⟩ := append_iff.mp h
  have hb : src e = b := hr.source_eq_of_cons
  exact ⟨left, right, rfl, hb ▸ hr.append hl⟩

private theorem rotate_append_cut_eq (left right : List β) :
    rot (left ++ right) left.length = right ++ left := by
  rw [rot_eq_drop_append_take_of_le _ _ (by simp)]
  simp

/-- Rotation at a chosen edge source, with a literal rotation index and the
complete occurrence inventory. -/
theorem exists_rotation_at_source {a : V} {es : List β}
    (h : EdgePath src dst a es a) {e : β} (he : e ∈ es) :
    ∃ j, j < es.length ∧ (rot es j).head? = some e ∧
      EdgePath src dst (src e) (rot es j) (src e) ∧ (rot es j).Perm es := by
  obtain ⟨left, right, hsplit, hp⟩ := h.rotate_at_mem he
  refine ⟨left.length, ?_, ?_, ?_, rot_perm es left.length⟩
  · simp [hsplit]
  · rw [hsplit, rotate_append_cut_eq]
    rfl
  · simpa only [hsplit, rotate_append_cut_eq] using hp

/-- Splice two cycles at a shared source vertex while preserving every edge
occurrence. Parallel edges and equal edge values are permitted. -/
theorem splice_at_shared_source {a b : V} {xs ys : List β}
    (hx : EdgePath src dst a xs a) (hy : EdgePath src dst b ys b)
    {e f : β} (he : e ∈ xs) (hf : f ∈ ys) (hshare : src e = src f) :
    ∃ zs, EdgePath src dst (src e) zs (src e) ∧ zs.Perm (xs ++ ys) ∧ zs ≠ [] := by
  obtain ⟨i, hi, hhead, hxr, hxp⟩ := hx.exists_rotation_at_source he
  obtain ⟨j, hj, _, hyr, hyp⟩ := hy.exists_rotation_at_source hf
  have hyr' : EdgePath src dst (src e) (rot ys j) (src e) := hshare ▸ hyr
  refine ⟨rot xs i ++ rot ys j, hxr.append hyr', hxp.append hyp, ?_⟩
  intro hz
  have hlen := congrArg List.length hz
  simp only [List.length_append, rot_length, List.length_nil] at hlen
  omega

/-- A destination vertex on a nonempty closed path is also the source of an
edge occurrence on that path. -/
theorem target_is_source {a : V} {es : List β} (h : EdgePath src dst a es a)
    {e : β} (he : e ∈ es) : ∃ f ∈ es, src f = dst e := by
  obtain ⟨left, right, hsplit, hp⟩ := h.rotate_at_mem he
  have ht := hp.tail_of_cons
  change EdgePath src dst (dst e) (right ++ left) (src e) at ht
  cases hrl : right ++ left with
  | nil =>
    rw [hrl] at ht
    exact ⟨e, he, ht.eq_of_nil.symm⟩
  | cons f fs =>
    rw [hrl] at ht
    refine ⟨f, ?_, ht.source_eq_of_cons⟩
    have hm : f ∈ right ++ left := by rw [hrl]; simp
    rw [hsplit]
    rcases List.mem_append.mp hm with hm | hm
    · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hm))
    · exact List.mem_append.mpr (Or.inl hm)

theorem source_of_incident {a v : V} {es : List β}
    (h : EdgePath src dst a es a) (hv : ∃ e ∈ es, src e = v ∨ dst e = v) :
    ∃ e ∈ es, src e = v := by
  obtain ⟨e, he, hsource | htarget⟩ := hv
  · exact ⟨e, he, hsource⟩
  · obtain ⟨f, hf, hfe⟩ := h.target_is_source he
    exact ⟨f, hf, hfe.trans htarget⟩

/-- Two closed cycles incident at a common vertex can be spliced; incidence
may be witnessed at either end of an edge. -/
theorem splice_at_shared_vertex {a b v : V} {xs ys : List β}
    (hx : EdgePath src dst a xs a) (hy : EdgePath src dst b ys b)
    (hvx : ∃ e ∈ xs, src e = v ∨ dst e = v)
    (hvy : ∃ e ∈ ys, src e = v ∨ dst e = v) :
    ∃ zs, EdgePath src dst v zs v ∧ zs.Perm (xs ++ ys) ∧ zs ≠ [] := by
  obtain ⟨e, he, hev⟩ := hx.source_of_incident hvx
  obtain ⟨f, hf, hfv⟩ := hy.source_of_incident hvy
  obtain ⟨zs, hp, hi, hn⟩ := hx.splice_at_shared_source hy he hf (hev.trans hfv.symm)
  exact ⟨zs, hev ▸ hp, hi, hn⟩

end EdgePath

/-- An explicit attachment order: each added cycle shares a vertex with the
accumulated edge inventory. This is a finite witness, not a graph convention. -/
def CycleAttachmentOrder (src dst : β → V) (first : List β) : List (List β) → Prop
  | [] => True
  | next :: rest =>
      (∃ v, (∃ e ∈ first, src e = v ∨ dst e = v) ∧
        (∃ e ∈ next, src e = v ∨ dst e = v)) ∧
      CycleAttachmentOrder src dst (first ++ next) rest

theorem CycleAttachmentOrder.congr_inventory {src dst : β → V}
    {first second : List β} {rest : List (List β)} (hp : first.Perm second) :
    CycleAttachmentOrder src dst first rest ↔ CycleAttachmentOrder src dst second rest := by
  induction rest generalizing first second with
  | nil => rfl
  | cons next rest ih =>
    simp only [CycleAttachmentOrder]
    constructor
    · intro ⟨⟨v, ⟨e, he, hev⟩, hn⟩, ht⟩
      exact ⟨⟨v, ⟨e, hp.mem_iff.mp he, hev⟩, hn⟩,
        (ih (hp.append_right next)).mp ht⟩
    · intro ⟨⟨v, ⟨e, he, hev⟩, hn⟩, ht⟩
      exact ⟨⟨v, ⟨e, hp.mem_iff.mpr he, hev⟩, hn⟩,
        (ih (hp.append_right next)).mpr ht⟩

/-- A finite family of closed cycles with an explicit shared-vertex
attachment order becomes one closed cycle with exactly the combined inventory.
The initial cycle may be empty only when the attachment witness allows it. -/
theorem EdgePath.splice_family {src dst : β → V} {a : V} {first : List β}
    {rest : List (List β)} (hf : EdgePath src dst a first a)
    (hr : ∀ cycle ∈ rest, ∃ v, EdgePath src dst v cycle v)
    (ha : CycleAttachmentOrder src dst first rest) :
    ∃ v es, EdgePath src dst v es v ∧ es.Perm (first ++ rest.flatten) := by
  induction rest generalizing a first with
  | nil => exact ⟨a, first, hf, by simp⟩
  | cons next rest ih =>
    obtain ⟨b, hb⟩ := hr next (by simp)
    obtain ⟨⟨v, hvf, hvn⟩, hat⟩ := ha
    obtain ⟨joined, hj, hp, _⟩ := hf.splice_at_shared_vertex hb hvf hvn
    have hnew : CycleAttachmentOrder src dst joined rest :=
      (CycleAttachmentOrder.congr_inventory hp).mpr hat
    obtain ⟨w, es, he, hep⟩ := ih hj
      (fun cycle hm => hr cycle (List.mem_cons_of_mem _ hm)) hnew
    refine ⟨w, es, he, hep.trans ?_⟩
    simpa only [List.flatten_cons, List.append_assoc] using hp.append_right rest.flatten

end SuperpermutationUpperBound
