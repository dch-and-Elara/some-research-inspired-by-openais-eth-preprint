import J6R10RepackPacketScope
import J6DeformationPoly
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-! A true zero-mode slot kills target exponents, even when the actual
crossing coefficients at the (nonzero) probe are not zero. -/
namespace J6R14ZeroMode
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid P11FullPacking
open DenominatorBudget J6R9PacketCoeff J6R9PacketLocal
noncomputable section

section Constants
variable {R G K M P : Type*} [CommRing R] [DecidableEq G] [DecidableEq K]
  [Fintype M] [DecidableEq M]

omit [DecidableEq G] [DecidableEq K] in
theorem row_constant (bit : Bool) (base : R) (cross : M → R) :
    MvPolynomial.constantCoeff (J6RecursiveModes.row bit base cross) =
      LiteralPortCompiler.affine bit base := by
  unfold J6RecursiveModes.row
  rw [map_add,MvPolynomial.constantCoeff_C,map_sum]
  have h (m : M) : (Finsupp.single m 1 : M →₀ ℕ) ≠ 0 := by
    intro he
    have hv := congrArg (fun x : M →₀ ℕ => x m) he
    simp at hv
  simp only [MvPolynomial.constantCoeff_monomial,if_neg (h _),Finset.sum_const_zero,add_zero]

/-- Keep the actual crossing values; the requested coefficient, not the
choice of numerical probe, erases their entire contribution at beta=0. -/
theorem packet_constant (target source : M → G × K) (g : G) (k : K)
    (ports : Finset P) (bit : P → Bool) (base : P → R)
    (cross : P → M → R) (moment : M → R) :
    J6RecursiveModes.packet target source g k ports bit base cross moment 0 =
      ∏ p ∈ ports, LiteralPortCompiler.affine (bit p) (base p) := by
  rw [J6RecursiveModes.packet,Finsupp.filter_zero,← MvPolynomial.constantCoeff_eq,map_prod]
  simp only [Finsupp.zero_apply,pow_zero,Finset.prod_const_one,mul_one,row_constant]
end Constants

section Degree
private theorem factors_degree (a : ℕ) (t : ℤ) (s : Finset ℤ) :
    (factors a t s).natDegree ≤ s.card := by
  unfold factors
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _q ∈ s, 1 := by
      refine Finset.sum_le_sum fun q _ => ?_
      exact (natDegree_add_le _ _).trans <|
        max_le (by simp) (natDegree_mul_le.trans (by simp))
    _ = _ := by simp

theorem W_degree (a : ℕ) (t k : ℤ) (ht : t ∈ grid a) (hk : k ∈ grid a) :
    (W a t k).natDegree ≤ 2*2^a-1 := by
  by_cases he : k=t
  · subst k
    rw [W,if_pos rfl]
    change (C (rho a t)*factors a t ((grid a).erase t)).natDegree ≤ _
    exact natDegree_mul_le.trans (by
      rw [natDegree_C,zero_add,← J6DeformationPoly.grid_card,
        ← Finset.card_erase_of_mem ht]
      exact factors_degree _ _ _)
  · rw [W,if_neg he]
    have hconstant : (C (rho a t)*C (J6ActiveLocalFactor.slope a t k)*X).natDegree ≤ 1 := by
      rw [← C_mul]
      exact natDegree_mul_le.trans (by simp only [natDegree_C,zero_add,natDegree_X,le_refl])
    have hkt : k ∈ (grid a).erase t := Finset.mem_erase.mpr ⟨he,hk⟩
    have hs := (factors_degree a t (((grid a).erase t).erase k))
    rw [Finset.card_erase_of_mem hkt,Finset.card_erase_of_mem ht,J6DeformationPoly.grid_card] at hs
    have hpa : 0 < (2:ℕ)^a := by positivity
    have hpos : 1 < 2*2^a := by omega
    exact natDegree_mul_le.trans ((Nat.add_le_add hconstant hs).trans (by omega))

end Degree

#print axioms row_constant
#print axioms packet_constant
#print axioms W_degree
end
end J6R14ZeroMode
