import SuperpermutationUpperBound.Transport.OrbitCounts
import SuperpermutationUpperBound.Transport.Closed
import Mathlib.Tactic.Ring

/-! The signed-excess ledger for subdivision of the wraparound port edge.
Only signed excess, not individual row or charge counts, is uniform. -/
namespace SuperpermutationUpperBound.Transport

variable {α β γ : Type}

/-- Row count minus total charge, with subtraction in the integers. -/
def signedExcess (rs : List (Row α)) : Int :=
  (rs.length : Int) - ((rs.map Row.charge).sum : Int)

theorem signedExcess_eq_neg_sum_delta (rs : List (Row α)) :
    signedExcess rs = -((rs.map delta).sum) := by
  rw [sum_delta]
  unfold signedExcess
  omega

@[simp] theorem fullAt_delta (r : Row α) (z : α) (j : Nat) :
    delta (fullAt r z j) = -1 := by
  simp [delta, Row.charge, fullAt]

@[simp] theorem shortAt_delta (r : Row α) (z : α) (j : Nat)
    (hn : 1 ≤ r.base.length) : delta (shortAt r z j) = 1 := by
  have he : r.base.length + 1 - (r.base.length - 1) = 2 := by omega
  simp [delta, Row.charge, shortAt, he]

@[simp] theorem shortLast_delta (r : Row α) (z : α)
    (hn : 1 ≤ r.base.length) : delta (shortLast r z) = 1 := by
  have he : r.base.length + 1 - (r.base.length - 1) = 2 := by omega
  simp [delta, Row.charge, shortLast, he]

/-- Each row on the local path retains the source row's displacement. -/
theorem portPath_sum_delta (r : Row α) (z : α) (j : Nat)
    (hn : 3 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ((portPath r z j).map delta).sum = ((portPath r z j).length : Int) * delta r := by
  rcases hkind with hf | hs
  · have hd : delta r = -1 := delta_full (by simp [Row.charge, hf])
    simp only [portPath, if_pos hf, fullPathAt, hd]
    split <;> simp
  · have hf : r.visible ≠ r.base.length := by omega
    have hc : r.charge = 2 := by unfold Row.charge; omega
    have hd : delta r = 1 := delta_short hc
    simp only [portPath, if_neg hf, shortPathAt, hd]
    split <;> simp [shortAt_delta r z _ (by omega), shortLast_delta r z (by omega)]

/-- Duplicating the wraparound crossing adds one displacement. Its correction
is a difference of consecutive port representatives, ready to telescope. -/
theorem portPath_local_winding (r : Row α) (z : α) (j : Nat)
    (hn : 3 ≤ r.base.length)
    (hkind : r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hj : j < r.base.length - 1) :
    ((r.base.length - 1 : Nat) : Int) * ((portPath r z j).map delta).sum =
      (r.base.length : Int) * delta r - ((portTarget r j : Int) - (j : Int)) := by
  rw [portPath_sum_delta r z j hn hkind]
  rcases hkind with hf | hs
  · have hd : delta r = -1 := delta_full (by simp [Row.charge, hf])
    by_cases hjzero : j = 0
    · subst j
      rw [portTarget_full_zero hn hf, hd]
      simp [portPath, hf, fullPathAt]
      omega
    · rw [portTarget_full_pos hn hf hj (by omega), hd]
      simp [portPath, hf, fullPathAt, hjzero]
      omega
  · have hf : r.visible ≠ r.base.length := by omega
    have hc : r.charge = 2 := by unfold Row.charge; omega
    have hd : delta r = 1 := delta_short hc
    by_cases hjsmall : j < r.base.length - 2
    · rw [portTarget_short_singleton hf hjsmall, hd]
      simp [portPath, hf, shortPathAt, hjsmall]
      omega
    · have hjeq : j = r.base.length - 2 := by omega
      subst j
      rw [portTarget_short_final hn hf, hd]
      simp [portPath, hf, shortPathAt]
      omega

/-- Summing local displacement ledgers telescopes the port representatives,
while keeping the literal concatenation of every local row path. -/
theorem orbitRows_winding_ledger (paths : β → List (Row α)) (next : β → β)
    (d v : β → Int) (P C : Int)
    (hlocal : ∀ ip, P * ((paths ip).map delta).sum = C * d ip - (v (next ip) - v ip))
    (start : β) (k : Nat) :
    P * ((orbitRows paths next start k).map delta).sum =
      C * ((orbitLabels next start k).map d).sum - (v (advance next start k) - v start) := by
  induction k generalizing start with
  | zero => simp [orbitRows, orbitLabels, advance]
  | succ k ih =>
    rw [orbitRows_succ, List.map_append, List.sum_append, mul_add, hlocal, ih]
    simp only [orbitLabels, List.map_cons, List.sum_cons, advance]
    ring

/-- A closed labeled orbit has no uncancelled port boundary term. -/
theorem orbitRows_closed_winding_ledger (paths : β → List (Row α)) (next : β → β)
    (d v : β → Int) (P C : Int)
    (hlocal : ∀ ip, P * ((paths ip).map delta).sum = C * d ip - (v (next ip) - v ip))
    (start : β) (k : Nat) (hreturn : advance next start k = start) :
    P * ((orbitRows paths next start k).map delta).sum =
      C * ((orbitLabels next start k).map d).sum := by
  simpa only [hreturn, sub_self, sub_zero] using
    orbitRows_winding_ledger paths next d v P C hlocal start k

/-- Split an orbit's occurrence list after a specified number of steps. -/
theorem orbitLabels_add (next : β → β) (start : β) (a b : Nat) :
    orbitLabels next start (a + b) =
      orbitLabels next start a ++ orbitLabels next (advance next start a) b := by
  induction a generalizing start with
  | zero => simp [orbitLabels, advance]
  | succ a ih =>
    simp only [Nat.succ_add, orbitLabels, advance, List.cons_append]
    rw [ih]

/-- Every consecutive whole lap visits every row occurrence exactly once,
even when the row values themselves are equal. -/
theorem cyclicFirst_lap_inventory (R : Nat) (hR : 0 < R)
    (S : Fin R × β → Fin R × β)
    (hfirst : ∀ ip, (S ip).1 = rowIndexPerm R hR ip.1) (ip : Fin R × β) :
    ((orbitLabels S ip R).map Prod.fst).Perm (List.finRange R) := by
  have hnodup : ((orbitLabels S ip R).map Prod.fst).Nodup := by
    rw [orbitLabels_eq_map_iterate, List.map_map]
    apply (List.nodup_map_iff_inj_on List.nodup_range).mpr
    intro i hi j hj heq
    have hv := congrArg Fin.val heq
    simp only [Function.comp_def, cyclicFirst_iterate_val R hR S hfirst] at hv
    exact (Nat.ModEq.add_left_cancel (Nat.ModEq.refl ip.1.val) hv).eq_of_lt_of_lt
      (List.mem_range.mp hi) (List.mem_range.mp hj)
  apply perm_of_nodup_subset_length hnodup
    (fun i _ => List.mem_finRange i) (by simp)

theorem cyclicFirst_lap_sum (R : Nat) (hR : 0 < R)
    (S : Fin R × β → Fin R × β)
    (hfirst : ∀ ip, (S ip).1 = rowIndexPerm R hR ip.1)
    (d : Fin R → Int) (ip : Fin R × β) :
    ((orbitLabels S ip R).map (fun jp => d jp.1)).sum = ((List.finRange R).map d).sum := by
  have he := ((cyclicFirst_lap_inventory R hR S hfirst ip).map d).sum_eq
  simpa only [List.map_map, Function.comp_def] using he

/-- A sequence of complete row laps accumulates the old-row displacement
sum once per lap, independently of its starting row and port. -/
theorem cyclicFirst_laps_sum (R : Nat) (hR : 0 < R)
    (S : Fin R × β → Fin R × β)
    (hfirst : ∀ ip, (S ip).1 = rowIndexPerm R hR ip.1)
    (d : Fin R → Int) (ip : Fin R × β) (k : Nat) :
    ((orbitLabels S ip (R * k)).map (fun jp => d jp.1)).sum =
      (k : Int) * ((List.finRange R).map d).sum := by
  induction k generalizing ip with
  | zero => simp [orbitLabels]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (R * k) R, orbitLabels_add, List.map_append,
      List.sum_append, cyclicFirst_lap_sum R hR S hfirst d, ih]
    simp only [Int.natCast_add, Int.natCast_one]
    ring

/-- Accumulated source displacement along whole laps of the actual successor. -/
theorem rowPortSuccessor_laps_sum_delta (rs : List (Row α)) (hR : 0 < rs.length)
    (h : Nat) (hn : 3 ≤ h + 2) (ip : Fin rs.length × Fin (h + 1)) (k : Nat) :
    ((orbitLabels (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]))
      ip (rs.length * k)).map (fun jp => delta rs[jp.1.val])).sum =
      (k : Int) * (rs.map delta).sum := by
  have hs := cyclicFirst_laps_sum rs.length hR
    (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]))
    (fun ip => rowPortSuccessor_fst hR (h + 2) hn _ ip)
    (fun i : Fin rs.length => delta rs[i.val]) ip k
  have hm := congrArg (fun rows => (rows.map delta).sum) (finRange_map_list_getElem rs)
  simp only [List.map_map, Function.comp_def] at hm
  rw [hm] at hs
  exact hs

/-- The actual successor realizes the local winding equation on literal
transported paths. -/
theorem rowPortSuccessor_local_winding (rs : List (Row α)) (hR : 0 < rs.length)
    (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (z : α) (ip : Fin rs.length × Fin (h + 1)) :
    ((h + 1 : Nat) : Int) * ((portPath rs[ip.1.val] z ip.2.val).map delta).sum =
      ((h + 2 : Nat) : Int) * delta rs[ip.1.val] -
        (((rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]) ip).2.val : Int) -
          (ip.2.val : Int)) := by
  have hr := hbase _ (List.getElem_mem ip.1.isLt)
  have hk := hkind _ (List.getElem_mem ip.1.isLt)
  have he := portPath_local_winding rs[ip.1.val] z ip.2.val (by omega) hk (by omega)
  rw [hr] at he
  rw [rowPortSuccessor_snd_val hR (h + 2) hn _
    (fun i => hbase _ (List.getElem_mem i.isLt))]
  simpa using he

/-- For a returning orbit consisting of k complete old-row laps, subdivision
multiplies the accumulated signed excess by new-size/port-count. -/
theorem rowPortSuccessor_closed_laps_winding (rs : List (Row α)) (hR : 0 < rs.length)
    (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (z : α) (ip : Fin rs.length × Fin (h + 1)) (k : Nat)
    (hreturn : advance
      (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]))
      ip (rs.length * k) = ip) :
    ((h + 1 : Nat) : Int) * signedExcess
      (orbitRows (fun jp : Fin rs.length × Fin (h + 1) => portPath rs[jp.1.val] z jp.2.val)
        (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]))
        ip (rs.length * k)) =
      ((h + 2 : Nat) : Int) * (k : Int) * signedExcess rs := by
  have he := orbitRows_closed_winding_ledger
    (fun jp : Fin rs.length × Fin (h + 1) => portPath rs[jp.1.val] z jp.2.val)
    (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]))
    (fun jp => delta rs[jp.1.val]) (fun jp => (jp.2.val : Int))
    ((h + 1 : Nat) : Int) ((h + 2 : Nat) : Int)
    (rowPortSuccessor_local_winding rs hR h hn hbase hkind z) ip (rs.length * k) hreturn
  have hsum := rowPortSuccessor_laps_sum_delta rs hR h hn ip k
  have he := he.trans (congrArg (fun a : Int => ((h + 2 : Nat) : Int) * a) hsum)
  rw [signedExcess_eq_neg_sum_delta, signedExcess_eq_neg_sum_delta]
  have hneg := congrArg Neg.neg he
  simp only [← mul_neg] at hneg
  rw [mul_assoc]
  exact hneg

/-- Each minimal returning label orbit has the paper's signed-excess scaling.
This multiplicative form records exactness before integer division. -/
theorem rowPortSuccessor_orbit_signedExcess_mul_gcd (rs : List (Row α))
    (hR : 0 < rs.length) (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (z : α) (ip : Fin rs.length × Fin (h + 1)) (k : Nat)
    (hsize : k = rs.length * ((h + 1) / Nat.gcd (h + 1) (signedExcess rs).natAbs))
    (hreturn : advance
      (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val])) ip k = ip) :
    (Nat.gcd (h + 1) (signedExcess rs).natAbs : Int) * signedExcess
      (orbitRows (fun jp : Fin rs.length × Fin (h + 1) => portPath rs[jp.1.val] z jp.2.val)
        (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val])) ip k) =
      ((h + 2 : Nat) : Int) * signedExcess rs := by
  subst k
  let c := Nat.gcd (h + 1) (signedExcess rs).natAbs
  let L := (h + 1) / c
  let e := signedExcess
    (orbitRows (fun jp : Fin rs.length × Fin (h + 1) => portPath rs[jp.1.val] z jp.2.val)
      (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val]))
      ip (rs.length * L))
  have hledger : ((h + 1 : Nat) : Int) * e =
      ((h + 2 : Nat) : Int) * (L : Int) * signedExcess rs :=
    rowPortSuccessor_closed_laps_winding rs hR h hn hbase hkind z ip L hreturn
  have hdivNat : c * L = h + 1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hdiv : (c : Int) * (L : Int) = ((h + 1 : Nat) : Int) := by
    simpa only [Int.natCast_mul] using congrArg (fun n : Nat => (n : Int)) hdivNat
  have hLpos : 0 < L := by
    change 0 < (h + 1) / Nat.gcd (h + 1) (signedExcess rs).natAbs
    rw [← shiftPort_minimalPeriod h (signedExcess rs) ⟨0, by omega⟩]
    exact Function.minimalPeriod_pos_of_mem_periodicPts
      ((shiftPortPerm h (signedExcess rs)).injective.mem_periodicPts _)
  have hLne : (L : Int) ≠ 0 := by omega
  change (c : Int) * e = ((h + 2 : Nat) : Int) * signedExcess rs
  apply mul_left_cancel₀ hLne
  calc
    (L : Int) * ((c : Int) * e) = ((c : Int) * (L : Int)) * e := by ring
    _ = ((h + 1 : Nat) : Int) * e := by rw [hdiv]
    _ = ((h + 2 : Nat) : Int) * (L : Int) * signedExcess rs := hledger
    _ = (L : Int) * (((h + 2 : Nat) : Int) * signedExcess rs) := by ring

/-- The signed excess of each literal transported minimal orbit is n*w/c,
for positive, zero, or negative old signed excess. -/
theorem rowPortSuccessor_orbit_signedExcess (rs : List (Row α))
    (hR : 0 < rs.length) (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (z : α) (ip : Fin rs.length × Fin (h + 1)) (k : Nat)
    (hsize : k = rs.length * ((h + 1) / Nat.gcd (h + 1) (signedExcess rs).natAbs))
    (hreturn : advance
      (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val])) ip k = ip) :
    signedExcess
      (orbitRows (fun jp : Fin rs.length × Fin (h + 1) => portPath rs[jp.1.val] z jp.2.val)
        (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val])) ip k) =
      (((h + 2 : Nat) : Int) * signedExcess rs) /
        (Nat.gcd (h + 1) (signedExcess rs).natAbs : Int) := by
  have he := rowPortSuccessor_orbit_signedExcess_mul_gcd rs hR h hn hbase hkind z ip k hsize hreturn
  have hcpos := Nat.gcd_pos_of_pos_left (signedExcess rs).natAbs (Nat.succ_pos h)
  have hcne : (Nat.gcd (h + 1) (signedExcess rs).natAbs : Int) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hcpos)
  rw [← he, Int.mul_ediv_cancel_left _ hcne]

/-- No supplied period or return premise is needed for the literal minimal
orbit of the actual successor. -/
theorem rowPortSuccessor_minimalOrbit_signedExcess (rs : List (Row α))
    (hR : 0 < rs.length) (h : Nat) (hn : 3 ≤ h + 2)
    (hbase : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (z : α) (ip : Fin rs.length × Fin (h + 1)) :
    signedExcess
      (orbitRows (fun jp : Fin rs.length × Fin (h + 1) => portPath rs[jp.1.val] z jp.2.val)
        (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val])) ip
        (Function.minimalPeriod
          (rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val])) ip)) =
      (((h + 2 : Nat) : Int) * signedExcess rs) /
        (Nat.gcd (h + 1) (signedExcess rs).natAbs : Int) := by
  apply rowPortSuccessor_orbit_signedExcess rs hR h hn hbase hkind z ip
  · exact rowPortSuccessor_list_minimalPeriod rs hR h hn hbase hkind ip
  · rw [advance_eq_iterate]
    exact Function.iterate_minimalPeriod

/-- Actual transport produces exactly c closed literal descendants, uses every
replacement row occurrence once, and gives each descendant signed excess
n*w/c. The multiplicative ledger is valid for every signed old excess. -/
theorem transport_closedTrail_winding {rs : List (Row α)} (z : α) (h : Nat)
    (hn : 3 ≤ h + 2) (hc : ClosedTrail rs)
    (hlen : ∀ r ∈ rs, r.base.length = h + 2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2) :
    ∃ trails : List (List (Row α)),
      (∀ trail ∈ trails, ClosedTrail trail) ∧
      trails.flatten.Perm (packingRows rs z) ∧
      trails.length = Nat.gcd (h + 1) (signedExcess rs).natAbs ∧
      ∀ trail ∈ trails,
        (Nat.gcd (h + 1) (signedExcess rs).natAbs : Int) * signedExcess trail =
          ((h + 2 : Nat) : Int) * signedExcess rs := by
  have hR : 0 < rs.length := List.length_pos_iff.mpr hc.1
  let σ := rowPortSuccessor hR (h + 2) hn (fun i : Fin rs.length => rs[i.val])
  let paths := fun ip : Fin rs.length × Fin (h + 1) => portPath rs[ip.1.val] z ip.2.val
  have hi (i : Fin rs.length) : (rs[i.val]).base.length = h + 2 :=
    hlen _ (List.getElem_mem i.isLt)
  have hk (i : Fin rs.length) := hkind _ (List.getElem_mem (l := rs) (n := i.val) i.isLt)
  have hne : ∀ ip, paths ip ≠ [] := fun ip => portPath_nonempty _ _ _
  have hinternal : ∀ ip, RowTrailCompatible ((paths ip).head (hne ip)) (paths ip).tail := by
    intro ip
    exact portPath_internal _ _ _ (by rw [hi]; omega)
  have hboundary : ∀ ip, ((paths ip).getLast (hne ip)).Compatible
      ((paths (σ ip)).head (hne (σ ip))) := by
    intro ip
    change ((portPath rs[ip.1.val] z ip.2.val).getLast _).tail =
      ((portPath rs[(σ ip).1.val] z (σ ip).2.val).head _).head
    rw [portPath_last_tail z (by rw [hi]; exact hn) (hk ip.1) (by rw [hi]; exact ip.2.isLt),
      portPath_head z (by rw [hi]; exact hn) (hk (σ ip).1)
        (by rw [hi]; exact (σ ip).2.isLt)]
    have hs : (σ ip).2.val = portTarget rs[ip.1.val] ip.2.val :=
      rowPortSuccessor_snd_val hR (h + 2) hn _ hi ip
    rw [hs]
    have hrow := closedTrail_getElem_compatible hc ip.1
    have hf : (σ ip).1.val = (ip.1.val + 1) % rs.length :=
      rowPortSuccessor_fst_val hR (h + 2) hn _ ip
    simp only [hf]
    rw [hrow]
  obtain ⟨orbits, hreturns, hpartition, hcount⟩ :=
    rowPortSuccessor_list_counted_orbit_partition rs hR h hn hlen hkind
  let trails := orbits.map (fun orbit => orbitRows paths σ orbit.1 orbit.2)
  refine ⟨trails, ?_, ?_, ?_, ?_⟩
  · intro trail ht
    obtain ⟨orbit, ho, rfl⟩ := List.mem_map.mp ht
    exact orbitRows_closedTrail_of_endpoints paths σ hne hinternal hboundary orbit.1
      (hreturns orbit ho).2.1 (hreturns orbit ho).2.2
  · have hp := hpartition.flatMap_right paths
    have hassoc := @List.flatMap_assoc ((Fin rs.length × Fin (h + 1)) × Nat)
      (Fin rs.length × Fin (h + 1)) (Row α) orbits
      (fun orbit => orbitLabels σ orbit.1 orbit.2) paths
    have he : trails.flatten = (orbits.flatMap (fun orbit => orbitLabels σ orbit.1 orbit.2)).flatMap paths := by
      exact hassoc.symm
    exact (List.Perm.of_eq he).trans (hp.trans (product_portPaths_inventory rs z (h + 2) hn hlen))
  · simpa only [trails, List.length_map, signedExcess] using hcount
  · intro trail ht
    obtain ⟨orbit, ho, rfl⟩ := List.mem_map.mp ht
    exact rowPortSuccessor_orbit_signedExcess_mul_gcd rs hR h hn hlen hkind z
      orbit.1 orbit.2 (hreturns orbit ho).1 (hreturns orbit ho).2.2

end SuperpermutationUpperBound.Transport
