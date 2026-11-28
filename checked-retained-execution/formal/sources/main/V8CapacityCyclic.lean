import V8CapacityCRTReadout
import Mathlib.LinearAlgebra.Isomorphisms

/-! The cyclic module in A4 is the actual image after multiplying by
the residual power. This uses ideal quotients and module first
isomorphism (not cardinal heuristics). -/
namespace V8CapacityCyclic
open V8CapacityCRTJet
noncomputable section

variable (O : Type*) [CommRing O] [IsDomain O]

theorem cancel_exact (π : O) (hπ : π≠0) (p a : ℕ) (ha : a≤p) (x : O) :
    π^p∣π^a*x ↔ π^(p-a)∣x := by
  have hp : p=a+(p-a) := (Nat.add_sub_of_le ha).symm
  conv_lhs => lhs; rw [hp,pow_add]
  exact mul_dvd_mul_iff_left (pow_ne_zero _ hπ)

def mulReduce (π : O) (p a : ℕ) : O →ₗ[O] BaseMod O π p where
  toFun x := coeffMod O π p (π^a*x)
  map_add' x y := by rw [mul_add,map_add]
  map_smul' r x := by
    change coeffMod O π p (π^a*(r*x)) = r • coeffMod O π p (π^a*x)
    rw [Algebra.smul_def, mul_left_comm (π^a) r, map_mul]
    rfl

theorem mulReduce_kernel (π : O) (hπ : π≠0) (p a : ℕ) (ha : a≤p) :
    LinearMap.ker (mulReduce O π p a) = (Ideal.span ({π^(p-a)} : Set O) : Submodule O O) := by
  ext x
  rw [LinearMap.mem_ker]
  change Ideal.Quotient.mk (Ideal.span ({π^p}:Set O)) (π^a*x)=0 ↔ x ∈ Ideal.span ({π^(p-a)}:Set O)
  simp only [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]
  exact cancel_exact O π hπ p a ha x

/-- The actual range ideal is isomorphic to O/π^(p-a), as an O-module
(and hence with the inherited finite-ring coefficient action). -/
def cyclicIso (π : O) (hπ : π≠0) (p a : ℕ) (ha : a≤p) :
    BaseMod O π (p-a) ≃ₗ[O] LinearMap.range (mulReduce O π p a) := by
  change (O ⧸ (Ideal.span ({π^(p-a)}:Set O) : Submodule O O)) ≃ₗ[O] _
  rw [← mulReduce_kernel O π hπ p a ha]
  exact LinearMap.quotKerEquivRange (mulReduce O π p a)

theorem quotient_modular_dvd (π : O) (hπ : π≠0) (p s L : ℕ) (x : O) :
    (∃ y : O, π^s∣π^L*(x+π^p*y)) ↔ π^(min p (s-L))∣x := by
  have aux (y : O) : π^s∣π^L*y ↔ π^(s-L)∣y := by
    by_cases h : L≤s
    · exact cancel_exact O π hπ s L h y
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h),pow_zero]
      exact iff_of_true ((pow_dvd_pow π (Nat.le_of_not_ge h)).trans (dvd_mul_right _ _)) (one_dvd _)
  constructor
  · rintro ⟨y,hy⟩
    have h₁ := (pow_dvd_pow π (min_le_right p (s-L))).trans ((aux _).mp hy)
    have h₂ := (pow_dvd_pow π (min_le_left p (s-L))).trans (dvd_mul_right _ y)
    simpa only [add_sub_cancel_right] using dvd_sub h₁ h₂
  · intro h
    by_cases hL : s-L≤p
    · rw [min_eq_right hL] at h
      refine ⟨0,(aux _).mpr ?_⟩
      simpa only [mul_zero,add_zero] using h
    · rw [min_eq_left (Nat.le_of_not_ge hL)] at h
      obtain ⟨z,hz⟩ := h
      refine ⟨-z,(aux _).mpr ?_⟩
      simp [hz]

#print axioms cancel_exact
#print axioms mulReduce_kernel
#print axioms cyclicIso
#print axioms quotient_modular_dvd
end
end V8CapacityCyclic
