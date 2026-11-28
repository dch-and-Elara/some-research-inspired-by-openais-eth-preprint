import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic

/-! Smith presentation of the actual image submodule over a local PID.
The polynomial feature construction does not enter this algebraic step. -/
namespace V8CapacitySmith
open scoped BigOperators Classical
open Module

noncomputable section

variable {O : Type*} [CommRing O] [IsDomain O]
variable [IsLocalRing O] [IsPrincipalIdealRing O]

theorem nonzero_is_pow_unit (π : O)
    (hMax : IsLocalRing.maximalIdeal O = Ideal.span ({π}:Set O)) (x : O) (hx : x≠0) :
    ∃ a : ℕ, ∃ u : Oˣ, x=π^a*(u:O) := by
  revert hx
  refine wellFounded_dvdNotUnit.induction (C:=fun y : O => y≠0 → ∃ a : ℕ, ∃ u : Oˣ, y=π^a*(u:O)) x ?_
  intro y ih hy
  by_cases hu : IsUnit y
  · exact ⟨0,hu.unit,by rw [pow_zero,one_mul,hu.unit_spec]⟩
  · have hy' : y∈IsLocalRing.maximalIdeal O := by
      by_contra hn
      exact hu ((IsLocalRing.notMem_maximalIdeal).mp hn)
    have hdiv : π∣y := by rwa [hMax,Ideal.mem_span_singleton] at hy'
    obtain ⟨v,hv⟩ := hdiv
    have hv0 : v≠0 := by intro hz; apply hy; rw [hv,hz,mul_zero]
    have hπ : ¬IsUnit π := by
      intro hU
      apply (IsLocalRing.notMem_maximalIdeal).mpr hU
      rw [hMax,Ideal.mem_span_singleton]
    have hrel : DvdNotUnit v y := ⟨hv0,π,hπ,hv.trans (mul_comm _ _)⟩
    obtain ⟨a,u,h⟩ := ih v hrel hv0
    refine ⟨a+1,u,?_⟩
    rw [hv,h,pow_succ',mul_assoc]

variable {M I : Type*} [AddCommGroup M] [Module O M] [Fintype I]
variable (π : O)

structure Powered (N : Submodule O M) (I : Type*) (n : ℕ) where
  chart : Module.Basis.SmithNormalForm N I n
  exponent : Fin n → ℕ
  unitCoeff : Fin n → Oˣ
  powerDiag : ∀ i, chart.a i=π^(exponent i)*(unitCoeff i:O)

omit [IsLocalRing O] [IsPrincipalIdealRing O] [Fintype I] in
theorem smith_diag_ne_zero {N : Submodule O M} {n : ℕ} (S : Module.Basis.SmithNormalForm N I n)
    (j : Fin n) : S.a j≠0 := by
  intro hz
  have h : (S.bN j : M)=0 := by rw [S.snf,hz,zero_smul]
  exact S.bN.ne_zero j (Subtype.ext h)

/-- For an actual finite free ambient module and any submodule, create a
Smith chart with genuine powers of the chosen uniformizer. No supplied
matrix diagonal or divisibility hypothesis remains. -/
def exists_powered (hMax : IsLocalRing.maximalIdeal O = Ideal.span ({π}:Set O))
    (base : Basis I O M) (N : Submodule O M) : Σ n, Powered π N I n := by
  obtain ⟨n,S⟩ := N.smithNormalForm base
  choose d u hu using (fun j : Fin n => nonzero_is_pow_unit π hMax (S.a j) (smith_diag_ne_zero S j))
  exact ⟨n,⟨S,d,u,hu⟩⟩

#print axioms nonzero_is_pow_unit
#print axioms smith_diag_ne_zero
#print axioms exists_powered
end
end V8CapacitySmith
