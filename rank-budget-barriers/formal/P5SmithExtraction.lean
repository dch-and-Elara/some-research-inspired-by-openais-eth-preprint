import P5ScalarReceipt
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! Smith factors of power-annihilated observations, using the ordinary
PID submodule Smith theorem, never Smith form over a jet algebra. -/
namespace Paper5
open scoped BigOperators Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem smith_of_power_killed {s : ℕ} {M : Type*} [AddCommGroup M] [Module R M]
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (K : ℕ) (f : (Fin s→R) →ₗ[R] M) (kill : ∀ x, π^K • f x = 0) :
    ∃ q : Fin s→ℕ, (∀ i,q i≤K) ∧ Nonempty (LinearMap.range f ≃ₗ[R] CyclicGrid π q) := by
  classical
  let N := LinearMap.ker f
  let a0 : (Fin s→R) →ₗ[R] N :=
    ((π^K) • (LinearMap.id : (Fin s→R) →ₗ[R] (Fin s→R))).codRestrict N fun x => by
      change f ((π^K) • x)=0
      rw [map_smul,kill]
  have ha0 : Function.Injective a0 := by
    intro x y h
    funext i
    have h' := congrFun (congrArg Subtype.val h) i
    change π^K * x i = π^K * y i at h'
    exact mul_left_cancel₀ (pow_ne_zero _ hπ) h'
  have hrank : Module.finrank R N = Module.finrank R (Fin s→R) :=
    le_antisymm (Submodule.finrank_le N) (LinearMap.finrank_le_finrank_of_injective ha0)
  obtain ⟨b,a,ab,hab⟩ := N.exists_smith_normal_form_of_rank_eq (Pi.basisFun R (Fin s)) hrank
  have hb (x : Fin s→R) : x ∈ N ↔ ∀ i, a i ∣ b.repr x i := by
    rw [ab.mem_submodule_iff']
    have hcoord (c : Fin s→R) (i : Fin s) : b.repr (∑ j, c j • (ab j : Fin s→R)) i = a i * c i := by
      simp only [hab,← mul_smul,b.repr_sum_self,mul_comm]
    constructor
    · rintro ⟨c,rfl⟩ i
      exact ⟨c i,hcoord c i⟩
    · intro hx
      choose c hc using hx
      exact ⟨c,b.ext_elem fun i => (hc i).trans (hcoord c i).symm⟩
  have hd (i : Fin s) : a i ∣ π^K := by
    have hx := (hb (π^K • b i)).mp (a0 (b i)).property i
    simpa using hx
  have hp : Prime π := (Ideal.span_singleton_prime hπ).mp hmax.isPrime
  choose q hq hass using fun i => (dvd_prime_pow hp K).mp (hd i)
  let D : (Fin s→R) →ₗ[R] CyclicGrid π q :=
    LinearMap.pi fun i =>
      ((Ideal.Quotient.mkₐ R (PowIdeal π (q i))).toLinearMap).comp
        ((LinearMap.proj i).comp b.equivFun.toLinearMap)
  have hD (x : Fin s→R) (i : Fin s) :
      D x i = Ideal.Quotient.mk (PowIdeal π (q i)) (b.repr x i) := rfl
  have hspan (i : Fin s) : Ideal.span ({a i}:Set R) = PowIdeal π (q i) :=
    Ideal.span_singleton_eq_span_singleton.mpr (hass i)
  have eker : N = LinearMap.ker D := by
    ext x
    rw [hb]
    constructor
    · intro hx
      change D x=0
      funext i
      rw [hD,Pi.zero_apply,Ideal.Quotient.eq_zero_iff_mem]
      rw [← hspan i]
      exact Ideal.mem_span_singleton.mpr (hx i)
    · intro hx i
      change D x=0 at hx
      have hi := congrFun hx i
      rw [hD,Pi.zero_apply,Ideal.Quotient.eq_zero_iff_mem] at hi
      rw [← hspan i] at hi
      exact Ideal.mem_span_singleton.mp hi
  have hsur : Function.Surjective D := by
    intro y
    choose x hx using fun i => (Ideal.Quotient.mk_surjective (I:=PowIdeal π (q i))) (y i)
    refine ⟨b.equivFun.symm x,?_⟩
    funext i
    rw [hD,show b.repr (b.equivFun.symm x) i = x i from congrFun (b.equivFun.apply_symm_apply x) i,hx]
  exact ⟨q,hq,⟨(LinearMap.quotKerEquivRange f).symm.trans
    ((Submodule.quotEquivOfEq N (LinearMap.ker D) eker).trans (LinearMap.quotKerEquivOfSurjective D hsur))⟩⟩

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem localJet_power_killed (π : R) {P K k : ℕ} (h : P≤K)
    (x : LocalJet π P k) : π^K • x = 0 := by
  have hmk : Ideal.Quotient.mk (PowIdeal π P) (π^K) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (pow_dvd_pow π h))
  rw [Algebra.smul_def]
  change (AdjoinRoot.of _ (Ideal.Quotient.mk (PowIdeal π P) (π^K))) * x = _
  rw [hmk,map_zero,zero_mul]

variable {T : Type*} [Fintype T]

theorem literal_observation_has_smith {s : ℕ}
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P k : T→ℕ) :
    ∃ q : Fin s→ℕ, (∀ i,q i≤Finset.univ.sup P) ∧ Nonempty
      (LinearMap.range (scalarObserve π t α P k s) ≃ₗ[R] CyclicGrid π q) := by
  apply smith_of_power_killed π hπ hmax
  intro x
  funext u
  exact localJet_power_killed π (Finset.le_sup (Finset.mem_univ u)) _

#print axioms smith_of_power_killed
#print axioms localJet_power_killed
#print axioms literal_observation_has_smith
end Paper5
