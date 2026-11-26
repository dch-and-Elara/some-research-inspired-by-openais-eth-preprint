import P5SmithExtraction
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! Valuations of the actual nonzero elementary factors of the
integral evaluation map, derived over every local PID domain.
Zero invariant factors are treated in a separate padded profile. -/
namespace Paper5.CommonJets
open Module
open scoped BigOperators Classical
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R]

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem irreducible_unit_uniformizer (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (a : R) (ha : Irreducible a) :
    ∃ u : Rˣ, a=(u:R)*π := by
  have hp : Prime π := (Ideal.span_singleton_prime hπ).mp hmax.isPrime
  have hm : a∈IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr ha.not_isUnit
  rw [←IsLocalRing.eq_maximalIdeal hmax] at hm
  obtain ⟨x,hx⟩ := Ideal.mem_span_singleton.mp hm
  have hu : IsUnit x := (ha.isUnit_or_isUnit hx).resolve_left hp.not_unit
  obtain ⟨u,rfl⟩ := hu
  exact ⟨u,hx.trans (mul_comm _ _)⟩

theorem pid_uniformizer_factor (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (a : R) (ha : a≠0) :
    ∃ s : ℕ,∃ u : Rˣ, a=(u:R)*π^s := by
  letI : WfDvdMonoid R := IsNoetherianRing.wfDvdMonoid
  apply WfDvdMonoid.induction_on_irreducible
    (motive:=fun a=>a≠0→∃ s : ℕ,∃ u : Rˣ,a=(u:R)*π^s) a ?_ ?_ ?_ ha
  · intro h
    exact False.elim (h rfl)
  · intro u hu _
    obtain ⟨v,rfl⟩ := hu
    exact ⟨0,v,by simp⟩
  · intro b i hb hi ih _
    obtain ⟨s,u,hu⟩ := ih hb
    obtain ⟨v,hv⟩ := irreducible_unit_uniformizer π hπ hmax i hi
    refine ⟨s+1,v*u,?_⟩
    rw [hu,hv,Units.val_mul,pow_succ]
    ring

variable {n r : ℕ}
theorem smith_power_factors (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (N : Submodule R (Fin n→R))
    (D : Basis.SmithNormalForm N (Fin n) r) :
    ∃ σ : Fin r→ℕ,∃ u : Fin r→Rˣ, ∀ i,D.a i=(u i:R)*π^(σ i) := by
  have hNe (i : Fin r) : D.a i≠0 := by
    intro hi
    apply D.bN.ne_zero i
    apply Subtype.ext
    simpa [hi] using D.snf i
  choose s u h using fun i=>pid_uniformizer_factor π hπ hmax (D.a i) (hNe i)
  exact ⟨s,u,h⟩

#print axioms irreducible_unit_uniformizer
#print axioms pid_uniformizer_factor
#print axioms smith_power_factors
end Paper5.CommonJets
