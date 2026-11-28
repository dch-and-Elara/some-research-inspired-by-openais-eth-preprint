import V8NativeMessageC3MainCoefficient
import J6ActiveHermite
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3700000

/-! MAIN's positive mesh and the coefficientwise extra loss of the actual
local Hermite reciprocal. No saturation in a finite coefficient ring is used. -/
namespace V8NativeMessage.C3.Hermite
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid J6ActiveUniqueness J6ActiveHermite
noncomputable section

def nodes (Q : ℕ) : Finset ℕ := Finset.Icc 1 Q
def logLoss (Q : ℕ) : ℕ := Nat.log 2 Q
def invDiff (v w : ℕ) : ℚ := ((v:ℚ)-(w:ℚ))⁻¹

theorem mesh_diff_abs {Q v w : ℕ} (hv : v∈nodes Q) (hw : w∈nodes Q) :
    ((v:ℤ)-(w:ℤ)).natAbs < Q := by
  have h₁ := Finset.mem_Icc.mp hv
  have h₂ := Finset.mem_Icc.mp hw
  omega

theorem diff_valuation {Q v w : ℕ} (hv : v∈nodes Q) (hw : w∈nodes Q)
    (hne : v≠w) : padicValInt 2 ((v:ℤ)-(w:ℤ))≤logLoss Q := by
  have h : (v:ℤ)-(w:ℤ)≠0 := by exact_mod_cast (sub_ne_zero.mpr (by exact_mod_cast hne) : (v:ℤ)-(w:ℤ)≠0)
  apply Nat.le_log_of_pow_le (by decide : 1<2)
  apply le_trans _ (mesh_diff_abs hv hw).le
  have he := Int.natAbs_le_of_dvd_ne_zero (padicValInt_dvd (p:=2) ((v:ℤ)-(w:ℤ))) h
  simpa only [Int.natAbs_pow,show Int.natAbs (2:ℤ)=2 by decide] using he

theorem invDiff_mul {v w : ℕ} (hne : v≠w) :
    invDiff v w * ((v:ℚ)-(w:ℚ))=1 := by
  unfold invDiff
  apply inv_mul_cancel₀
  exact sub_ne_zero.mpr (by exact_mod_cast hne)

theorem scaled_invDiff {Q v w : ℕ} (hv : v∈nodes Q) (hw : w∈nodes Q)
    (hne : v≠w) : (2:ℚ)^logLoss Q * invDiff v w ∈ twoLocalSubalgebra := by
  have h : (v:ℤ)-(w:ℤ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  obtain ⟨z,hz,hfact⟩ := integer_odd_factor h
  have hzQ : (z:ℚ)≠0 := by exact_mod_cast odd_int_ne_zero hz
  let ν := padicValInt 2 ((v:ℤ)-(w:ℤ))
  have hν : ν≤logLoss Q := diff_valuation hv hw hne
  have hzOdd : ¬(2:ℤ)∣z := fun he => (Int.not_even_iff_odd.mpr hz) (even_iff_two_dvd.mpr he)
  have hInv : ((z:ℚ)⁻¹) ∈ twoLocalSubalgebra :=
    (mem_twoLocal_iff _).mpr ⟨1,z,hzOdd,by simp⟩
  have hcast : (v:ℚ)-(w:ℚ) = (2:ℚ)^ν*(z:ℚ) := by
    dsimp [ν]
    unfold pow₂ at hfact
    exact_mod_cast hfact
  have hpow : (2:ℚ)^logLoss Q = (2:ℚ)^(logLoss Q-ν)*(2:ℚ)^ν := by
    rw [← pow_add,Nat.sub_add_cancel hν]
  have he : (2:ℚ)^logLoss Q * invDiff v w = (2:ℚ)^(logLoss Q-ν)*(z:ℚ)⁻¹ := by
    rw [invDiff,hcast,hpow]
    field_simp
  rw [he]
  have htwo : (2:ℚ)∈twoLocalSubalgebra := (mem_twoLocal_iff _).mpr ⟨2,1,by decide,by simp⟩
  exact twoLocalSubalgebra.mul_mem (twoLocalSubalgebra.pow_mem htwo _) hInv

def carrier (Q J v : ℕ) : ℚ[X] :=
  normalizer (nodes Q) (fun i => (i:ℚ)) (fun _ => J) invDiff v

def normalized (Q J v : ℕ) : ℚ[X] :=
  atNode (1:ℚˣ) (v:ℚ) (carrier Q J v)

theorem normalized_expansion (Q J v : ℕ) :
    normalized Q J v = ∏ w ∈ (nodes Q).erase v, (1+C (invDiff v w)*X)^J := by
  unfold normalized carrier normalizer
  simp only [map_prod,map_pow]
  refine Finset.prod_congr rfl (fun w hw => congrArg (·^J) ?_)
  have ne : v≠w := (Finset.mem_erase.mp hw).1.symm
  simp only [atNode_apply,coord,Units.val_one,C_1,one_mul,mul_comp,C_comp,sub_comp,X_comp]
  rw [add_sub_assoc,← C_sub,mul_add,← C_mul,invDiff_mul ne,C_1,add_comm]

theorem normalized_constant (Q J v : ℕ) : (normalized Q J v).coeff 0 = 1 := by
  exact normalizer_at_own (nodes Q) (fun i => (i:ℚ)) (fun _ => J) invDiff v 1
    (fun w hw => invDiff_mul (Finset.mem_erase.mp hw).1.symm)

def dilation (c : ℕ) : ℚ[X] →+* ℚ[X] := Polynomial.compRingHom (C ((2:ℚ)^c)*X)

theorem dilation_coeff (c : ℕ) (p : ℚ[X]) (k : ℕ) :
    (dilation c p).coeff k = (2:ℚ)^(c*k)*p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add,coeff_add,hp,hq,coeff_add,mul_add]
  | monomial j x =>
    change ((monomial j x).comp (C ((2:ℚ)^c)*X)).coeff k =
      (2:ℚ)^(c*k)*(monomial j x).coeff k
    rw [monomial_comp,mul_pow,← C_pow,← mul_assoc,← C_mul,coeff_C_mul_X_pow,coeff_monomial]
    by_cases h : k=j
    · subst k
      simp [pow_mul,mul_comm]
    · simp [h,Ne.symm h]

def localPolyImage : Subring ℚ[X] := (mapRingHom twoLocalRat).range

theorem coeff_in_local_of_poly (p : ℚ[X]) (hp : p∈localPolyImage) (k : ℕ) :
    p.coeff k∈twoLocalSubalgebra := by
  obtain ⟨q,hq⟩ := hp
  change q.map twoLocalRat=p at hq
  rw [← hq,coeff_map]
  exact (q.coeff k).property

theorem scaled_normalized_integral {Q v : ℕ} (J : ℕ) (hv : v∈nodes Q) :
    dilation (logLoss Q) (normalized Q J v) ∈ localPolyImage := by
  rw [normalized_expansion,map_prod]
  refine localPolyImage.prod_mem (fun w hw => ?_)
  rw [map_pow]
  refine localPolyImage.pow_mem ?_ _
  have h := Finset.mem_erase.mp hw
  let q : TwoLocal := ⟨(2:ℚ)^logLoss Q*invDiff v w,scaled_invDiff hv h.2 h.1.symm⟩
  refine ⟨1+C q*X,?_⟩
  change (1+C q*X).map twoLocalRat =
    (1+C (invDiff v w)*X).comp (C ((2:ℚ)^logLoss Q)*X)
  simp only [Polynomial.map_add,Polynomial.map_one,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_X,add_comp,one_comp,mul_comp,C_comp,X_comp,← mul_assoc,← C_mul]
  congr 2
  apply congrArg C
  change (2:ℚ)^logLoss Q*invDiff v w = invDiff v w*(2:ℚ)^logLoss Q
  exact mul_comm _ _

def invLocal (Q J v : ℕ) : ℚ[X] := geomInverse J (normalized Q J v)

theorem invLocal_is_inverse (Q J v : ℕ) :
    (X:ℚ[X])^J ∣ normalized Q J v * invLocal Q J v - 1 :=
  geom_inverse_mod J _ (normalized_constant Q J v)

/-- If w=v the reciprocal is not consulted; the finite mesh has no
collision. Each retained reciprocal coefficient has the proposed loss
k⌊log₂Q⌋, including the endpoints and the Q=1 empty carrier. -/
theorem invLocal_coeff_loss {Q v : ℕ} (J k : ℕ) (hv : v∈nodes Q) :
    (2:ℚ)^(logLoss Q*k) * (invLocal Q J v).coeff k ∈ twoLocalSubalgebra := by
  rw [← dilation_coeff]
  apply coeff_in_local_of_poly
  unfold invLocal geomInverse
  simp only [map_sum,map_pow,map_sub,map_one]
  exact localPolyImage.sum_mem (fun i _ =>
    localPolyImage.pow_mem (localPolyImage.sub_mem localPolyImage.one_mem
      (scaled_normalized_integral J hv)) _)

#print axioms mesh_diff_abs
#print axioms diff_valuation
#print axioms scaled_invDiff
#print axioms normalized_expansion
#print axioms dilation_coeff
#print axioms scaled_normalized_integral
#print axioms invLocal_is_inverse
#print axioms invLocal_coeff_loss
end
end V8NativeMessage.C3.Hermite