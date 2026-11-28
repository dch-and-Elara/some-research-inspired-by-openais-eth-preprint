import J9R13PhysicalFusion

/-! Unfold the original J9 compiler into the same two-cube, one-mark
sum as the physically realized packet slot. No assumed readout
callback and no changes to the underlying two Boolean assignments. -/
namespace J6R14SpecializedBox
open scoped BigOperators Classical Polynomial
open Polynomial LiteralPortCompiler J9LayoutTransfer MvPolynomial
noncomputable section
set_option linter.unusedSectionVars false
variable {I R A K : Type*} [Fintype R] [Fintype I] [CommRing A] [CommRing K]

theorem one_mark_row_compiler (u k : Port R→A) :
    coeff β (rowCompiler u k) =
      ∑ y : Port R→Bool, (truth (allRows (R:=R)) y : A) *
        ∑ r : Port R, (LiteralPortCompiler.slope (y r) * k r) *
          ∏ r' ∈ (Finset.univ : Finset (Port R)).erase r, affine (y r') (u r') := by
  rw [rowCompiler,β,singleton_coeff]
  refine Finset.sum_congr rfl ?_
  intro Y _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _
  apply congrArg (fun q : A => truth (allRows (R:=R)) Y * q)
  let T (q : Port R) := portTerm Y (fun _ => u) (fun _ p (_:Unit) => k p) q (atPort r () q)
  change (∏ q, T q) = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
  congr 1
  · simp [T,atPort,portTerm]
  · refine Finset.prod_congr rfl ?_
    intro q hq
    have hn := (Finset.mem_erase.mp hq).1
    simp [T,atPort,portTerm,hn]

theorem map_affine_ring (φ : A→+*K) (b : Bool) (x : A) :
    φ (affine b x) = affine b (φ x) := by
  cases b <;> simp [affine]

theorem map_slope_ring (φ : A→+*K) (b : Bool) : φ (LiteralPortCompiler.slope b) = LiteralPortCompiler.slope b := by
  cases b <;> simp [LiteralPortCompiler.slope]

theorem evaluated_compiler_sum
    (φ : A→+*K) (s : K) (F : CNF I)
    (u k : (I→Bool)→Port R→A) (z : (I→Bool)→A) :
    s * φ (coeff β (completed (J9R13Compiler.system F)
      (J9R13Compiler.base u z) (J9R13Compiler.kernel (fun x r (_:Unit) => k x r)))) =
    ∑ x : I→Bool, ∑ y : Port R→Bool,
      ((truth (allRows (R:=R)) y : K) * truth F x) *
        ∑ r : Port R, ((LiteralPortCompiler.slope (y r) * (s * φ (k x r))) * φ (z x)) *
          ∏ j ∈ (Finset.univ : Finset (Port R)).erase r, affine (y j) (φ (u x j)) := by
  rw [J9R13Compiler.singleton_separate,map_sum,Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [one_mark_row_compiler,map_mul,map_sum,Finset.mul_sum,Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [map_mul,map_mul,map_sum]
  simp only [map_truth]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _
  simp only [map_mul,map_prod,map_affine_ring,map_slope_ring]
  ring

#print axioms one_mark_row_compiler
#print axioms evaluated_compiler_sum
end
end J6R14SpecializedBox