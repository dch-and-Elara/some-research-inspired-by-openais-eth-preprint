import HermiteJetTransport
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Fixed Hermite weights for the actual translated Taylor coefficients.
Do not treat a quotient coefficient in the unshifted basis as a Hasse
coordinate. The proof passes through X^j divisibility after translation. -/
namespace P5MainBalance
open Polynomial
open scoped BigOperators Classical

noncomputable def center (t : ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun p := p.comp (X+C t)
  map_add' _ _ := add_comp
  map_smul' a p := by simp only [smul_eq_C_mul, C_mul_comp, RingHom.id_apply]

theorem shifted_coeffs_jet_zero (t : ℚ) (j : ℕ) (p : ℚ[X])
    (h : ∀ i < j,(center t p).coeff i=0) :
    HermiteJetTransport.jet t j p=0 := by
  apply (HermiteJetTransport.jet_zero_iff t j p).mpr
  have hw : (X:ℚ[X])^j ∣ center t p := X_pow_dvd_iff.mpr h
  obtain ⟨w,hw⟩ := hw
  refine ⟨w.comp (X-C t),?_⟩
  have hs : (X+C t : ℚ[X]).comp (X-C t)=X := by
    rw [add_comp,X_comp,C_comp]
    ring
  have he := congrArg (fun u : ℚ[X] => u.comp (X-C t)) hw
  simpa only [center,LinearMap.coe_mk,AddHom.coe_mk,comp_assoc,hs,comp_X,
    mul_comp,pow_comp,X_comp,HermiteJetTransport.nodePower] using he

variable {I : Type*} [Fintype I]

abbrev JetIndex (j : I→ℕ) := Σ i:I, Fin (j i)

noncomputable def coefficientJets (t : I→ℚ) (j : I→ℕ) :
    degreeLT ℚ (∑ i,j i) →ₗ[ℚ] (JetIndex j→ℚ) :=
  LinearMap.pi fun a => (lcoeff ℚ a.2).comp ((center (t a.1)).comp (degreeLT ℚ (∑ i,j i)).subtype)

theorem coefficientJets_injective (t : I→ℚ) (ht : Function.Injective t) (j : I→ℕ) :
    Function.Injective (coefficientJets t j) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro p hp
  apply Subtype.ext
  change (p:ℚ[X])=0
  apply HermiteJetTransport.zero_of_all_jets t ht j (mem_degreeLT.mp p.property)
  intro i
  apply shifted_coeffs_jet_zero
  intro z hz
  exact congrFun hp ⟨i,⟨z,hz⟩⟩

theorem weights_apply_linear {A : Type*} [Fintype A] (f : (A→ℚ)→ₗ[ℚ] ℚ)
    (x : A→ℚ) :
    f x = ∑ a, f (Pi.single a 1) * x a := by
  have hx : (∑ a : A, x a • (Pi.single a (1:ℚ) : A→ℚ))=x := by
    funext i
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  conv_lhs => rw [←hx]
  simp [map_sum,smul_eq_mul,mul_comm]

/-- The weights depend only on the nodes and their retained orders;
they work for every sign word and for every V-coordinate slice. -/
theorem actual_hermite_weights (t : I→ℚ) (ht : Function.Injective t) (j : I→ℕ) :
    ∃ w : JetIndex j→ℚ, ∀ p : ℚ[X], p.degree<↑(∑ i,j i) →
      p.eval 0 = ∑ a : JetIndex j,w a*(center (t a.1) p).coeff a.2 := by
  let J := coefficientJets t j
  obtain ⟨D,hD⟩ := J.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (coefficientJets_injective t ht j))
  let f : (JetIndex j→ℚ)→ₗ[ℚ] ℚ := (lcoeff ℚ 0).comp ((degreeLT ℚ (∑ i,j i)).subtype.comp D)
  refine ⟨fun a=>f (Pi.single a 1),?_⟩
  intro p hp
  let q : degreeLT ℚ (∑ i,j i) := ⟨p,mem_degreeLT.mpr hp⟩
  have h : D (J q)=q := by
    exact DFunLike.congr_fun hD q
  calc
    _ = f (J q) := by unfold f; simp only [LinearMap.comp_apply,h,Submodule.subtype_apply,q,lcoeff_apply,coeff_zero_eq_eval_zero]
    _ = _ := by
      rw [weights_apply_linear f (J q)]
      apply Finset.sum_congr (by ext a; simp)
      intro a _
      have ha : (J q) a=(center (t a.1) p).coeff a.2 := rfl
      rw [ha]
      apply congrArg (fun z : ℚ => z*((center (t a.1) p).coeff a.2))
      apply congrArg f
      funext i
      by_cases h : i=a <;> simp [Pi.single_apply,h]

#print axioms shifted_coeffs_jet_zero
#print axioms coefficientJets_injective
#print axioms weights_apply_linear
#print axioms actual_hermite_weights
end P5MainBalance
