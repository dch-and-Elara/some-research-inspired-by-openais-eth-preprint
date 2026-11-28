import NativeProbeRing
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement

/-! Existence of the original monic integer defining polynomial, with all
lower coordinates in {0,1}. The original enumeration's runtime is not
proved here. -/

namespace BinaryModulus
open Polynomial
open scoped BigOperators Polynomial IntermediateField

theorem irreducible_degree (e : ℕ) (he : 0 < e) :
    ∃ g : (ZMod 2)[X], g.Monic ∧ Irreducible g ∧ g.natDegree = e := by
  let K := GaloisField 2 e
  obtain ⟨α,hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) K
  have hInt : IsIntegral (ZMod 2) α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly (ZMod 2) α, minpoly.monic hInt, minpoly.irreducible hInt, ?_⟩
  rw [← IntermediateField.adjoin.finrank hInt, hα, IntermediateField.finrank_top']
  exact GaloisField.finrank 2 he.ne'

noncomputable def binaryLift (g : (ZMod 2)[X]) : ℤ[X] :=
  ∑ i ∈ g.support, monomial i ((g.coeff i).val : ℤ)

theorem coeff_binaryLift (g : (ZMod 2)[X]) (j : ℕ) :
    (binaryLift g).coeff j = ((g.coeff j).val : ℤ) := by
  rw [binaryLift, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    exact Polynomial.coeff_monomial_of_ne _ hi.symm
  · intro h
    have hg : g.coeff j = 0 := Polynomial.notMem_support_iff.mp h
    simp [hg]

theorem binaryLift_reduces (g : (ZMod 2)[X]) :
    NativeProbeRing.residuePoly (binaryLift g) = g := by
  ext j
  rw [NativeProbeRing.residuePoly, Polynomial.coeff_map, coeff_binaryLift]
  change (((g.coeff j).val : ℤ) : ZMod 2) = g.coeff j
  simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (g.coeff j)

theorem binaryLift_degree (g : (ZMod 2)[X]) (hg : g.Monic) :
    (binaryLift g).natDegree = g.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · unfold binaryLift
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans (Polynomial.le_natDegree_of_mem_supp i hi)
  · rw [coeff_binaryLift, Polynomial.coeff_natDegree, hg.leadingCoeff]
    decide

theorem binaryLift_monic (g : (ZMod 2)[X]) (hg : g.Monic) :
    (binaryLift g).Monic := by
  rw [Polynomial.Monic, ← Polynomial.coeff_natDegree, binaryLift_degree g hg,
    coeff_binaryLift, Polynomial.coeff_natDegree, hg.leadingCoeff]
  decide

theorem exists_printed_modulus (e : ℕ) (he : 0 < e) :
    ∃ f : ℤ[X], f.Monic ∧ Irreducible (NativeProbeRing.residuePoly f) ∧
      f.natDegree = e ∧ ∀ j : ℕ, f.coeff j = 0 ∨ f.coeff j = 1 := by
  obtain ⟨g,hm,hi,hd⟩ := irreducible_degree e he
  refine ⟨binaryLift g, binaryLift_monic g hm, ?_, (binaryLift_degree g hm).trans hd, ?_⟩
  · rwa [binaryLift_reduces]
  · intro j
    rw [coeff_binaryLift]
    have hb := ZMod.val_lt (g.coeff j)
    omega

/-- Existence of the source's actual permissible modulus and sufficient
binary representatives for its printed root count bound. -/
theorem printed_root_choices (s d : ℕ) (hs : 2 ≤ s) (hd : d ≤ s^4) :
    ∃ f : ℤ[X], f.Monic ∧ Irreducible (NativeProbeRing.residuePoly f) ∧
      f.natDegree = 4*Nat.clog 2 s ∧
      (∀ j : ℕ, f.coeff j = 0 ∨ f.coeff j = 1) ∧ d ≤ 2^f.natDegree := by
  have hpos := Nat.clog_pos (by decide : 1 < 2) hs
  obtain ⟨f,hm,hir,he,hbits⟩ := exists_printed_modulus (4*Nat.clog 2 s) (by omega)
  refine ⟨f,hm,hir,he,hbits,?_⟩
  rw [he]
  exact NativeProbeRing.printed_fit s _ d (Nat.le_pow_clog (by decide) s) hd

#print axioms printed_root_choices
#print axioms irreducible_degree
#print axioms binaryLift_reduces
#print axioms binaryLift_degree
#print axioms binaryLift_monic
#print axioms exists_printed_modulus

end BinaryModulus