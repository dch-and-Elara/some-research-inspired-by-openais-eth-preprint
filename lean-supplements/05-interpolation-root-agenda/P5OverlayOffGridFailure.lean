import P5HermiteTransportGenericH1
import P5H4SharpComplete

/-! The information-theoretic failure at insufficient total order:
two actual degree-bounded polynomials have identical scaled jets and
different off-grid evaluation. No linearity of a decoder is assumed. -/
namespace Paper5.HermiteExamples
open Polynomial Paper5.HermiteGeneric P5H4
open scoped BigOperators Polynomial Classical

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 6000000

noncomputable section
variable {K : Type*} [Field K]

def scaledData (s : Finset K) (k : K→ℕ) (α : K→K) (p : K[X]) :
    (t : s)→Fin (k t.val)→K := fun t=>scalarObserve t.val (α t.val) (k t.val) p

theorem allocated_same_scaled_data_as_zero (s : Finset K) (k : K→ℕ) (α : K→K) :
    scaledData s k α (allocated s k)=scaledData s k α 0 := by
  funext t i
  have ho : rootMultiplicity t.val (allocated s k)=k t.val := by
    rw [allocated_order,if_pos t.property]
  obtain ⟨q,hq⟩ := (le_rootMultiplicity_iff ((allocated_monic s k).ne_zero)).1 ho.ge
  have hshift : affinePolynomial t.val (α t.val) (X-C t.val)=(C (α t.val))*X := by
    change (X-C t.val).comp (C t.val+C (α t.val)*X)=C (α t.val)*X
    rw [sub_comp,X_comp,C_comp]
    ring
  have hz : X^(k t.val) ∣ affinePolynomial t.val (α t.val) (allocated s k) := by
    rw [hq,map_mul,map_pow,hshift,mul_pow]
    refine ⟨(C (α t.val))^(k t.val)*affinePolynomial t.val (α t.val) q,?_⟩
    ac_rfl
  unfold scaledData
  rw [scalarObserve_apply,scalarObserve_apply,map_zero,coeff_zero]
  exact (Polynomial.X_pow_dvd_iff.mp hz) _ i.isLt

theorem no_off_grid_decoder_when_degree_allows_vanishing_product
    (s : Finset K) (k : K→ℕ) (α : K→K) (a : K)
    (ha : a∉s) (d : ℕ) (degreeRoom : (∑t∈s,k t)≤d) :
    ¬∃ recover : ((t : s)→Fin (k t.val)→K)→K,
      ∀ p : K[X],p.natDegree≤d → recover (scaledData s k α p)=p.eval a := by
  rintro ⟨recover,correct⟩
  have hd : (allocated s k).natDegree≤d := by simpa only [allocated_degree] using degreeRoom
  apply allocated_eval_ne s k a ha
  calc
    (allocated s k).eval a = recover (scaledData s k α (allocated s k)) := (correct _ hd).symm
    _ = recover (scaledData s k α 0) := congrArg recover (allocated_same_scaled_data_as_zero s k α)
    _ = 0 := by simpa only [eval_zero] using correct 0 (by simp)

#print axioms allocated_same_scaled_data_as_zero
#print axioms no_off_grid_decoder_when_degree_allows_vanishing_product
end
end Paper5.HermiteExamples
