import SuperpermutationUpperBound.CircleTransport.Transport

namespace SuperpermutationUpperBound.Certificates.CircleBase
open CircleTransport Transport

structure MixedPointer where
  component : Nat
  port : Nat
  circle : Nat
  row : Nat
  localPort : Nat
  rotation : Nat
  deriving DecidableEq, Repr

structure OrdinaryPointer where
  component : Nat
  circle : Nat
  rotation : Nat
  base : List Nat
  active : Nat
  deriving DecidableEq, Repr

def componentAt (family : List (List (Row Nat))) (i : Nat) : List (Row Nat) :=
  family[i]?.getD []

def circleAt (circles : List (List Nat)) (i : Nat) : List Nat := circles[i]?.getD []

def rowAt (rs : List (Row Nat)) (i : Nat) : Row Nat := rs[i]?.getD ⟨[],0,0⟩

theorem componentAt_eq_getElem (family : List (List (Row Nat))) (i : Nat)
    (hi : i < family.length) : componentAt family i = family[i] := by
  simp only [componentAt, List.getElem?_eq_getElem hi, Option.getD_some]

theorem circleAt_mem (circles : List (List Nat)) (i : Nat) (hi : i < circles.length) :
    circleAt circles i ∈ circles := by
  simp only [circleAt, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem componentAt_mem (family : List (List (Row Nat))) (i : Nat) (hi : i < family.length) :
    componentAt family i ∈ family := by
  rw [componentAt_eq_getElem family i hi]
  exact List.getElem_mem hi

def MixedPointer.Valid (family : List (List (Row Nat))) (circles : List (List Nat))
    (final h : Nat) (p : MixedPointer) : Prop :=
  p.component < family.length ∧ p.port < h ∧ p.circle < circles.length ∧
    p.row < (componentAt family p.component).length ∧ final ∈ circleAt circles p.circle ∧
    p.rotation < (circleAt circles p.circle).length ∧
    completionExit ((componentAt family p.component).take p.row) p.port = p.localPort ∧
    rot (circleAt circles p.circle) p.rotation =
      insertLetter (rowAt (componentAt family p.component) p.row).head final p.localPort

instance (family : List (List (Row Nat))) (circles : List (List Nat)) (final h : Nat)
    (p : MixedPointer) : Decidable (p.Valid family circles final h) := by
  unfold MixedPointer.Valid
  infer_instance

def OrdinaryPointer.Valid (family : List (List (Row Nat))) (circles : List (List Nat))
    (satellite : Nat) (p : OrdinaryPointer) : Prop :=
  p.component < family.length ∧ p.circle < circles.length ∧
    p.rotation < (circleAt circles p.circle).length ∧
    rot (circleAt circles p.circle) p.rotation = p.base ∧
    componentAt family p.component = Partition.fullChart p.base p.active satellite

instance (family : List (List (Row Nat))) (circles : List (List Nat)) (satellite : Nat)
    (p : OrdinaryPointer) : Decidable (p.Valid family circles satellite) := by
  unfold OrdinaryPointer.Valid
  infer_instance

/-- A checked row occurrence and propagated port identify an actual head in
the completed designated trail. Only literal equality is used. -/
theorem MixedPointer.sound {family : List (List (Row Nat))} {circles : List (List Nat)}
    {final h : Nat} {p : MixedPointer} (hp : p.Valid family circles final h)
    (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ componentAt family p.component, r.base.length = h + 1)
    (hkind : ∀ r ∈ componentAt family p.component,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    SafeIncidence (componentAt family p.component) final ⟨p.port, hp.2.1⟩
      (circleAt circles p.circle) := by
  obtain ⟨_hcomp, hport, _hcircle, hrow, hfinal, hrot, hexit, hvertex⟩ := hp
  let rs := componentAt family p.component
  have hdecomp : rs = rs.take p.row ++ rowAt rs p.row :: rs.drop (p.row + 1) := by
    have he := List.take_append_drop p.row rs
    rw [List.drop_eq_getElem_cons (l := rs) hrow] at he
    have hg : rowAt rs p.row = rs[p.row]'hrow := by
      unfold rowAt
      rw [List.getElem?_eq_getElem (l := rs) hrow]
      rfl
    rw [hg]
    exact he.symm
  have he := completionExit_eq_oldWalk (rs.take p.row) h hn
    (fun r hr => hlen r (List.mem_of_mem_take hr))
    (fun r hr => hkind r (List.mem_of_mem_take hr)) ⟨p.port, hport⟩
  have hb : BoundaryVertex rs final h (by omega) ⟨p.port, hport⟩
      (insertLetter (rowAt rs p.row).head final p.localPort) := by
    refine ⟨rs.take p.row, rowAt rs p.row, rs.drop (p.row + 1), hdecomp, ?_⟩
    rw [← he, hexit]
  exact Or.inl ⟨hfinal, _, hb.mem_completionWalk hn hlen hkind, ⟨⟨p.rotation, hrot⟩, hvertex⟩⟩

theorem OrdinaryPointer.sound {family : List (List (Row Nat))} {circles : List (List Nat)}
    {satellite final h : Nat} {p : OrdinaryPointer} (hp : p.Valid family circles satellite)
    (j : Fin h) :
    SafeIncidence (componentAt family p.component) final j (circleAt circles p.circle) := by
  obtain ⟨_, _, hrot, hvertex, he⟩ := hp
  exact Or.inr ⟨p.base, p.active, satellite, ⟨⟨p.rotation, hrot⟩, hvertex⟩, he⟩

/-- Finite index coverage and checked occurrence pointers imply the semantic
cover of every tagged designated trail. No endpoint uniqueness is required. -/
theorem pointers_safe_cover (family : List (List (Row Nat))) (circles : List (List Nat))
    (final satellite h : Nat) (hn : 3 ≤ h + 1)
    (mixed : List MixedPointer) (ordinary : List OrdinaryPointer)
    (hlen : ∀ rs ∈ family, ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ rs ∈ family, ∀ r ∈ rs,
      r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hm : ∀ p ∈ mixed, p.Valid family circles final h)
    (ho : ∀ p ∈ ordinary, p.Valid family circles satellite)
    (hc : ∀ i : Fin family.length, ∀ j : Fin h,
      (∃ p ∈ mixed, p.component = i.val ∧ p.port = j.val) ∨
        (∃ p ∈ ordinary, p.component = i.val)) :
    SafeCircleCover (fun i : Fin family.length => componentAt family i.val) final h circles := by
  intro i j
  rcases hc i j with ⟨p, hp, hci, hpj⟩ | ⟨p, hp, hci⟩
  · have hv := hm p hp
    have hs := p.sound hv hn
      (hlen _ (componentAt_mem family p.component hv.1))
      (hkind _ (componentAt_mem family p.component hv.1))
    have he : (⟨p.port, hv.2.1⟩ : Fin h) = j := Fin.ext hpj
    rw [he] at hs
    rw [hci] at hs
    exact ⟨circleAt circles p.circle, circleAt_mem circles p.circle hv.2.2.1, hs⟩
  · have hv := ho p hp
    have hs := p.sound (final := final) hv j
    rw [hci] at hs
    exact ⟨circleAt circles p.circle, circleAt_mem circles p.circle hv.2.1, hs⟩

end SuperpermutationUpperBound.Certificates.CircleBase
