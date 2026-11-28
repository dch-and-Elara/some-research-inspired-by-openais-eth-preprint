import V8CapacityNewtonGrid
import V8CapacityMatrixImage

/-! Integrate A2 with A4: a normalized target is readable on the full
digit chart exactly when it belongs to the saturated actual weighted
Newton matrix image, with no additional point-value aliasing. -/
namespace V8CapacityIntegrated
open scoped Classical BigOperators
open V8CapacityDigits V8CapacityFactorial V8CapacityNewtonGrid V8CapacitySmith

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 650000

variable {O E I J : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [Fintype E] [Fintype I] [Fintype J] [LinearOrder I]
variable {π : O} {q : ℕ}
variable (D : Digits π q) (hq : 0<q) (hq₂ : 2≤q)
variable (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (degree : I → E → ℕ)
variable (order : ∀ i j, (∀ e, degree i e≤degree j e) → i≤j)

def weighted (π : O) (q : ℕ) (ν : I → E → ℕ) (C : Matrix I J O) : Matrix I J O :=
  Matrix.of fun i j => π^multiDebt q (ν i)*C i j

def rawAt (C : Matrix I J O) (a : J → O) (x : E → O) : O :=
  ∑ i : I, tensor D hq (degree i) x * (C.mulVec a i)

theorem rawAt_normalized (C : Matrix I J O) (a : J → O) (x : E → O) :
    rawAt D hq degree C a x = evalNormalized D hq hq₂ h0 hπ degree ((weighted π q degree C).mulVec a) x := by
  unfold rawAt evalNormalized
  apply Finset.sum_congr rfl
  intro i _
  rw [tensor_factor D hq hq₂ h0 hπ]
  simp only [Matrix.mulVec,weighted,Matrix.of_apply,dotProduct,mul_assoc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem eval_difference (w v : I → O) (e : O) (x : E → O) :
    evalNormalized D hq hq₂ h0 hπ degree w x-e*evalNormalized D hq hq₂ h0 hπ degree v x =
      evalNormalized D hq hq₂ h0 hπ degree (fun i => w i-e*v i) x := by
  simp only [evalNormalized,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

include hMax order in
theorem exact_readability (C : Matrix I J O) (L p : ℕ) (v : I → O) :
    (∃ a : J → O, ∀ x : E → O, π^(L+p)∣
      rawAt D hq degree C a x-π^L*evalNormalized D hq hq₂ h0 hπ degree v x) ↔
      realizable π L p (matrixImage (weighted π q degree C)) v := by
  let W := weighted π q degree C
  let J₀ := Ideal.span ({π^(L+p)}:Set O)
  have each (a : J → O) :
      (∀ x : E → O, π^(L+p)∣rawAt D hq degree C a x-
        π^L*evalNormalized D hq hq₂ h0 hπ degree v x) ↔
      ∀ i : I, π^(L+p)∣W.mulVec a i-π^L*v i := by
    simp_rw [rawAt_normalized D hq hq₂ h0 hπ,eval_difference D hq hq₂ h0 hπ]
    simpa only [J₀,Ideal.mem_span_singleton] using (all_values_iff_newton_coeff D hq hq₂ h0 hπ hMax degree order J₀
      (fun i => W.mulVec a i-π^L*v i))
  constructor
  · rintro ⟨a,ha⟩
    choose b hb using (each a).mp ha
    refine ⟨b,⟨a,?_⟩⟩
    funext i
    change W.mulVec a i = π^L*(v i+π^p*b i)
    calc
      _ = (W.mulVec a i-π^L*v i)+π^L*v i := by ring
      _ = _ := by rw [hb i,pow_add]; ring
  · rintro ⟨b,⟨a,ha⟩⟩
    refine ⟨a,(each a).mpr (fun i => ?_)⟩
    have h := congrFun ha i
    change W.mulVec a i=π^L*(v i+π^p*b i) at h
    rw [h]
    refine ⟨b i,?_⟩
    rw [pow_add]
    ring

include hq₂ h0 hπ hMax order in
theorem all_readable_output_integral_coefficients (C : Matrix I J O)
    (a : J → O) (L : ℕ) (integral : ∀ x : E → O, π^L∣rawAt D hq degree C a x) :
    ∀ i : I, π^L∣(weighted π q degree C).mulVec a i := by
  simp_rw [rawAt_normalized D hq hq₂ h0 hπ] at integral
  have h := all_values_iff_newton_coeff D hq hq₂ h0 hπ hMax degree order
    (Ideal.span ({π^L}:Set O)) ((weighted π q degree C).mulVec a)
  simp only [Ideal.mem_span_singleton] at h
  exact h.mp integral

#print axioms rawAt_normalized
#print axioms eval_difference
#print axioms exact_readability
#print axioms all_readable_output_integral_coefficients
end
end V8CapacityIntegrated
