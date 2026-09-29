import SuperpermutationUpperBound.Assembly.CycleConnectivity
import SuperpermutationUpperBound.Transport.FiniteOrbits
import Mathlib.Data.Fintype.EquivFin

namespace SuperpermutationUpperBound
variable {E V : Type} [Fintype E] [DecidableEq V]

/-- Degree balance counts labelled incoming and outgoing occurrences. -/
def BalancedDegrees (src dst : E → V) : Prop :=
  ∀ v, Fintype.card {e // dst e = v} = Fintype.card {e // src e = v}

/-- Match incoming to outgoing labels separately at each vertex. -/
noncomputable def balancedSuccessor (src dst : E → V) (hb : BalancedDegrees src dst) : Equiv.Perm E :=
  (Equiv.sigmaFiberEquiv dst).symm.trans
    ((Equiv.sigmaCongrRight (fun v => Fintype.equivOfCardEq (hb v))).trans
      (Equiv.sigmaFiberEquiv src))

theorem balancedSuccessor_boundary (src dst : E → V) (hb : BalancedDegrees src dst) (e : E) :
    dst e = src (balancedSuccessor src dst hb e) := by
  exact (Fintype.equivOfCardEq (hb (dst e)) ⟨e, rfl⟩).property.symm

/-- Every returning orbit of an endpoint-compatible successor is a directed
closed cycle. The orbit retains edge occurrences even for loops or parallel edges. -/
theorem edgePath_orbitLabels {src dst : E → V} (next : E → E)
    (hb : ∀ e, dst e = src (next e)) (start : E) (k : Nat) :
    EdgePath src dst (src start) (Transport.orbitLabels next start k)
      (src (Transport.advance next start k)) := by
  induction k generalizing start with
  | zero => exact .nil _
  | succ k ih =>
    refine .cons rfl ?_
    rw [hb start]
    exact ih (next start)

/-- A finite directed multigraph with degree balance decomposes into closed
cycles using every labelled edge exactly once. Connectivity is not required. -/
theorem balanced_graph_cycle_decomposition [DecidableEq E]
    (src dst : E → V) (hb : BalancedDegrees src dst) :
    ∃ cycles : List (List E),
      (∀ es ∈ cycles, es ≠ [] ∧ ∃ v, EdgePath src dst v es v) ∧
      cycles.flatten.Perm Finset.univ.toList := by
  let σ := balancedSuccessor src dst hb
  obtain ⟨orbits, hp, hi⟩ := Transport.invariant_finset_orbit_partition σ Finset.univ (by simp)
  refine ⟨orbits.map (fun orbit => Transport.orbitLabels σ orbit.1 orbit.2), ?_, ?_⟩
  · intro es hes
    obtain ⟨orbit, ho, rfl⟩ := List.mem_map.mp hes
    refine ⟨?_, src orbit.1, ?_⟩
    · have hl := Transport.orbitLabels_length σ orbit.1 orbit.2
      have hpos := (hp orbit ho).1
      intro hz
      rw [hz] at hl
      simp only [List.length_nil] at hl
      omega
    · have hh := edgePath_orbitLabels σ (balancedSuccessor_boundary src dst hb) orbit.1 orbit.2
      rw [(hp orbit ho).2] at hh
      exact hh
  · exact hi

end SuperpermutationUpperBound
