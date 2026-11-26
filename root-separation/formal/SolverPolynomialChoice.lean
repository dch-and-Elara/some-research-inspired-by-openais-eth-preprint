
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section
namespace RootSeparation.Solver
open Polynomial
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

structure SourcePolynomial (e : ℕ) where
  f : ℤ[X]
  monic : f.Monic
  degree : f.natDegree = e
  binary : ∀ k, f.coeff k = 0 ∨ f.coeff k = 1
  irreducibleTwo : Irreducible (f.map (Int.castRingHom (ZMod 2)))

/-- Integer lift with the mandatory binary coefficients, at the
    original degree. No choice of the field characteristic is made here. -/
def binaryLift (g : (ZMod 2)[X]) : ℤ[X] :=
  ∑ i ∈ Finset.range (g.natDegree+1), monomial i ((g.coeff i).val : ℤ)

theorem binaryLift_coeff (g : (ZMod 2)[X]) (i : ℕ) :
    (binaryLift g).coeff i = ((g.coeff i).val : ℤ) := by
  unfold binaryLift
  rw [finset_sum_coeff]
  by_cases hi : i ∈ Finset.range (g.natDegree+1)
  · rw [Finset.sum_eq_single_of_mem i hi]
    · simp
    · intro j _ hj
      simp [coeff_monomial, hj]
  · have hj : g.natDegree < i := by
      simp only [Finset.mem_range] at hi
      omega
    rw [coeff_eq_zero_of_natDegree_lt hj]
    apply Finset.sum_eq_zero
    intro j hj'
    have hne : j ≠ i := fun h => hi (h ▸ hj')
    simp [coeff_monomial,hne]

theorem binaryLift_map (g : (ZMod 2)[X]) : (binaryLift g).map (Int.castRingHom (ZMod 2)) = g := by
  ext i
  rw [coeff_map,binaryLift_coeff]
  change ((↑(g.coeff i).val : ℤ) : ZMod 2) = _
  rw [Int.cast_natCast]
  exact (ZMod.natCast_val _).trans (ZMod.cast_id _ _)

theorem binaryLift_monic (g : (ZMod 2)[X]) (hg : g.Monic) : (binaryLift g).Monic := by
  have he : (binaryLift g).natDegree = g.natDegree := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [binaryLift_coeff, coeff_eq_zero_of_natDegree_lt hn, ZMod.val_zero, Int.natCast_zero]
    · rw [binaryLift_coeff,hg.coeff_natDegree]
      decide
  unfold Monic leadingCoeff
  rw [he,binaryLift_coeff,hg.coeff_natDegree]
  decide

theorem sourcePolynomial_exists (e : ℕ) (he : 0 < e) : Nonempty (SourcePolynomial e) := by
  have he0 : e ≠ 0 := he.ne'
  let F := GaloisField 2 e
  letI : Finite F := inferInstanceAs (Finite (GaloisField 2 e))
  obtain ⟨α,hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) F
  let g := minpoly (ZMod 2) α
  have hInt : IsIntegral (ZMod 2) α := IsIntegral.of_finite _ _
  have hg : g.Monic := minpoly.monic hInt
  have hdeg : g.natDegree = e :=
    ((Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) α).1 hα).trans
      (GaloisField.finrank 2 he0)
  let f := binaryLift g
  have hf : f.Monic := binaryLift_monic g hg
  refine ⟨⟨f,hf,?_,?_,?_⟩⟩
  · exact (hf.natDegree_map (Int.castRingHom (ZMod 2))).symm.trans
      (by rw [binaryLift_map]; exact hdeg)
  · intro i
    change (binaryLift g).coeff i = 0 ∨ (binaryLift g).coeff i = 1
    rw [binaryLift_coeff]
    have h := ZMod.val_lt (g.coeff i)
    omega
  · change Irreducible ((binaryLift g).map _)
    rw [binaryLift_map]
    exact minpoly.irreducible hInt

#print axioms binaryLift_map
#print axioms binaryLift_monic
#print axioms sourcePolynomial_exists

end RootSeparation.Solver

