import J6RecursiveModes
import Mathlib.Data.Finsupp.Antidiagonal

/-! Identify the actual printed packet's Finsupp.singleton register:
one distinguished target port (or none), and one literal source moment
(or none). The other modes are not deleted from the row polynomial. -/
namespace J6R14SpecializedBox
open scoped BigOperators Classical
open MvPolynomial

noncomputable section
variable {R M I : Type*} [CommRing R]

theorem mv_zero_mul (F H : MvPolynomial M R) :
    coeff 0 (F*H) = coeff 0 F * coeff 0 H := by
  classical
  rw [coeff_mul,Finsupp.antidiagonal_zero]
  simp

theorem mv_single_mul (m : M) (F H : MvPolynomial M R) :
    coeff (Finsupp.single m 1) (F*H) =
      coeff (Finsupp.single m 1) F * coeff 0 H +
        coeff 0 F * coeff (Finsupp.single m 1) H := by
  classical
  rw [coeff_mul,Finsupp.antidiagonal_single,Finset.sum_map]
  have h : Finset.antidiagonal (1:ℕ) = {(0,1),(1,0)} := by decide
  rw [h]
  simp [add_comm]

theorem mv_zero_prod (s : Finset I) (F : I→MvPolynomial M R) :
    coeff 0 (∏ i ∈ s,F i) = ∏ i ∈ s, coeff 0 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi,mv_zero_mul,ih]

theorem mv_single_prod (m : M) (s : Finset I) (F : I→MvPolynomial M R) :
    coeff (Finsupp.single m 1) (∏ i ∈ s,F i) =
      ∑ i ∈ s, coeff (Finsupp.single m 1) (F i) *
        ∏ j ∈ s.erase i, coeff 0 (F j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : (Finsupp.single m (1:ℕ)) ≠ 0 := by
      intro he
      have hc := congrArg (fun β : M→₀ℕ => β m) he
      simp at hc
    simp [coeff_one,Ne.symm h]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,mv_single_mul,mv_zero_prod,ih,Finset.sum_insert hi,
      Finset.erase_insert hi,Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j≠i := fun h => hi (h ▸ hj)
    have he : i ∉ s.erase j := fun h => hi (Finset.mem_erase.mp h).2
    rw [Finset.erase_insert_of_ne (Ne.symm hji),Finset.prod_insert he]
    ring

variable [Fintype M] [DecidableEq M]

theorem mv_packet_row_zero (bit : Bool) (base : R) (cross : M→R) :
    coeff 0 (J6RecursiveModes.row bit base cross) = LiteralPortCompiler.affine bit base := by
  classical
  simp [J6RecursiveModes.row,coeff_add,coeff_sum,coeff_monomial]

theorem mv_packet_row_single (m : M) (bit : Bool) (base : R) (cross : M→R) :
    coeff (Finsupp.single m 1) (J6RecursiveModes.row bit base cross) =
      LiteralPortCompiler.slope bit * cross m := by
  classical
  have hn : (Finsupp.single m (1:ℕ)) ≠ 0 := by
    intro he
    have hc := congrArg (fun β : M→₀ℕ => β m) he
    simp at hc
  rw [J6RecursiveModes.row,coeff_add,coeff_C,if_neg (Ne.symm hn),zero_add,coeff_sum]
  rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _)]
  · simp
  · intro j _ hj
    have h : Finsupp.single j (1:ℕ) ≠ Finsupp.single m 1 := by
      intro he
      have h0 := congrArg (fun β : M→₀ℕ => β j) he
      simp [hj] at h0
    simp [coeff_monomial,h]

variable {G K P : Type*} [DecidableEq G] [DecidableEq K]

omit [Fintype M] in
private theorem restrict_single (m : M) (Q : M→Prop) [DecidablePred Q] :
    (Finsupp.single m (1:ℕ)).filter Q = if Q m then Finsupp.single m 1 else 0 := by
  ext k
  by_cases h : k=m
  · subst k
    by_cases hQ : Q m <;> simp [hQ]
  · by_cases hQ : Q m <;> simp [hQ,Finsupp.single_eq_of_ne h]

omit [DecidableEq M] in
private theorem source_single_factor (m : M) (Q : M→Prop) [DecidablePred Q] (v : M→R) :
    (∏ j ∈ Finset.univ.filter Q,v j ^ Finsupp.single m (1:ℕ) j) =
      if Q m then v m else 1 := by
  classical
  by_cases h : Q m
  · rw [if_pos h,Finset.prod_eq_single_of_mem m (by simp [h])]
    · simp
    · intro j _ hj
      simp [Finsupp.single_eq_of_ne hj]
  · rw [if_neg h]
    refine Finset.prod_eq_one ?_
    intro j hj
    have hn : j≠m := fun he => h (he ▸ (Finset.mem_filter.mp hj).2)
    simp [Finsupp.single_eq_of_ne hn]

theorem packet_exact_singleton (target source : M→G×K) (m : M) (g : G) (k : K)
    (ports : Finset P) (bit : P→Bool) (base : P→R) (cross : P→M→R) (mom : M→R) :
    J6RecursiveModes.packet target source g k ports bit base cross mom (Finsupp.single m 1) =
      (if target m=(g,k) then
        ∑ p ∈ ports, (LiteralPortCompiler.slope (bit p)*cross p m) *
         ∏ q ∈ ports.erase p, LiteralPortCompiler.affine (bit q) (base q)
       else ∏ p ∈ ports, LiteralPortCompiler.affine (bit p) (base p)) *
      (if source m=(g,k) then mom m else 1) := by
  classical
  rw [J6RecursiveModes.packet,restrict_single,source_single_factor]
  by_cases h : target m=(g,k)
  · simp only [if_pos h,mv_single_prod,mv_packet_row_zero,mv_packet_row_single]
  · simp only [if_neg h,mv_zero_prod,mv_packet_row_zero]

#print axioms mv_zero_mul
#print axioms mv_single_mul
#print axioms mv_zero_prod
#print axioms mv_single_prod
#print axioms mv_packet_row_zero
#print axioms mv_packet_row_single
#print axioms packet_exact_singleton
end
end J6R14SpecializedBox
