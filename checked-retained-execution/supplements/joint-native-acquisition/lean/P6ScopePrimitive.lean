import P6JointPartition
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open scoped Polynomial Classical BigOperators
open Polynomial NativeProbeRing
namespace P6Joint
noncomputable section

/-- A nonzero coefficient after stripping its exact dyadic factor and
retaining a unit necessarily survives a precision above that factor. -/
theorem dyadic_unit_survives (p v : ℕ) (hv : v < p)
    (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    (u : Scalar p f) (hu : IsUnit u) :
    (2 : Scalar p f)^v * u ≠ 0 := by
  have hp : 0 < p := by omega
  let j : Base p →+* Scalar p f := AdjoinRoot.of (liftPoly p f)
  have inj : Function.Injective j := (projectBase_left p hp f hf hd).injective
  have hn : (2 : Base p)^v ≠ 0 := by
    intro hz
    have hmod : (2:ℕ)^p ∣ (2:ℕ)^v := by
      exact (ZMod.natCast_eq_zero_iff _ _).mp (by exact_mod_cast hz)
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) (Nat.pow_lt_pow_right (by decide) hv)) hmod
  rcases hu with ⟨uu, rfl⟩
  intro h
  apply hn
  apply inj
  have h0 := congrArg (fun w : Scalar p f => w * ↑uu⁻¹) h
  simpa [j, mul_assoc] using h0

/-- Width of explicit tabulation comes from distinct incident old
vertices, not merely port count. A degree-three pin-free support
with q surviving ports forces a factor scope with at least q/3
old variables under the ordinary coefficient-support convention. -/
theorem surviving_ports_le_three_scope {Port Vertex : Type*} [DecidableEq Vertex]
    (ports : Finset Port) (vertex : Port → Vertex)
    (bounded : ∀ v, (ports.filter (fun p => vertex p = v)).card ≤ 3) :
    ports.card ≤ 3 * (ports.image vertex).card := by
  classical
  calc
    ports.card = ∑ v ∈ ports.image vertex, (ports.filter (fun p => vertex p = v)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ hp => Finset.mem_image_of_mem _ hp)
    _ ≤ ∑ _ ∈ ports.image vertex, 3 := Finset.sum_le_sum fun v _ => bounded v
    _ = _ := by simp [Nat.mul_comm]

#print axioms surviving_ports_le_three_scope

/-- A useful sufficient certificate for dense ordinary row scope: all
listed coefficients have a nonzero power-of-two times unit witness below
the requested precision. No claim that an optimized row representation
must materialize this scope. -/
theorem supported_scope_from_units {Port Vertex : Type*} [DecidableEq Vertex]
    (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    (ports : Finset Port) (vert : Port → Vertex) (W : Port → Scalar p f)
    (certificate : ∀ j ∈ ports, ∃ t < p, ∃ u, IsUnit u ∧ W j = 2^t * u)
    (bounded : ∀ v, (ports.filter (fun j => vert j = v)).card ≤ 3) :
    (∀ j ∈ ports, W j ≠ 0) ∧ ports.card ≤ 3 * (ports.image vert).card := by
  refine ⟨?_, surviving_ports_le_three_scope ports vert bounded⟩
  intro j hj
  obtain ⟨t,ht,u,hu,wu⟩ := certificate j hj
  rw [wu]
  exact dyadic_unit_survives p t ht f hf hd u hu

#print axioms supported_scope_from_units

#print axioms dyadic_unit_survives
end
end P6Joint
