import P5LiteralJets
import P5RepeatedObservation

/-! Literal local-jet capacities in (A.10), including zero precision or
zero retained order. The length is computed over the underlying domain. -/
namespace Paper5
open scoped BigOperators Polynomial
open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

theorem actual_jet_length (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (P k : ℕ) : Module.length R (LocalJet π P k) = (k*P:ℕ) := by
  by_cases hp : P=0
  · subst P
    haveI : Subsingleton (Cyclic π 0) := by
      have htop : PowIdeal π 0 = (⊤:Ideal R) := by
        change Ideal.span ({π^0}:Set R) = ⊤
        rw [pow_zero,Ideal.span_singleton_one]
      change Subsingleton (R ⧸ PowIdeal π 0)
      rw [htop]
      infer_instance
    haveI : Subsingleton (LocalJet π 0 k) := ⟨fun x y => by
      obtain ⟨a,rfl⟩ := AdjoinRoot.mk_surjective x
      obtain ⟨b,rfl⟩ := AdjoinRoot.mk_surjective y
      exact congrArg _ (Subsingleton.elim a b)⟩
    simp
  · have hpow : PowIdeal π P ≤ Ideal.span ({π}:Set R) := by
      apply Ideal.span_singleton_le_span_singleton.mpr
      simpa only [pow_one] using pow_dvd_pow π (show 1≤P by omega)
    have hp' : Ideal.span ({π} : Set R) ≠ ⊤ := (Ideal.isMaximal_def.mp hmax).1
    letI : Nontrivial (Cyclic π P) := by
      apply Ideal.Quotient.nontrivial
      intro hh
      apply hp'
      exact top_unique (hh ▸ hpow)
    let e := (AdjoinRoot.powerBasisAux' (Polynomial.monic_X_pow (R:=Cyclic π P) k)).equivFun.restrictScalars R
    rw [e.length_eq,Module.length_pi_of_fintype]
    simp [Polynomial.natDegree_X_pow,cyclic_length π hπ hmax]

theorem jet_factor_length {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (r k P : ℕ) (f : A →ₗ[R] B)
    (g : A →ₗ[R] (Fin r→LocalJet π P k))
    (h : (Fin r→LocalJet π P k) →ₗ[R] B)
    (fac : f = h.comp g) :
    Module.length R (LinearMap.range f) ≤ (r*k*P:ℕ) := by
  have hi : LinearMap.range f ≤ LinearMap.range h := by
    intro x hx
    obtain ⟨a,rfl⟩ := hx
    exact ⟨g a, by rw [fac]; rfl⟩
  have hh : Function.Surjective h.rangeRestrict := by
    intro y
    obtain ⟨a,ha⟩ := y.property
    exact ⟨a,Subtype.ext ha⟩
  have hj := Module.length_le_of_injective (Submodule.inclusion hi) (Submodule.inclusion_injective hi)
  have hk := Module.length_le_of_surjective h.rangeRestrict hh
  refine hj.trans (hk.trans_eq ?_)
  rw [Module.length_pi_of_fintype]
  simp [actual_jet_length π hπ hmax,Nat.mul_assoc]

#print axioms actual_jet_length
#print axioms jet_factor_length
end Paper5
