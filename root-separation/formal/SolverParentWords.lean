import SolverPhysicalSample
import SolverIntegralArithmetic
import SolverKernelWords

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial Classical
open scoped BigOperators

variable {s : ℕ} (F : SourcePolynomial (4*lambda s))
variable {c : Call F.f} (G : CallLayout s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^(4*lambda s))
variable (t : callCenters s c) (j : callProbes s c)

theorem rowLinearAt_integral (X : c.network.Wire → Bool) (x : c.network.Wire) :
    0 ≤ rationalValuation F (rowLinearAt F G cap t j X x) := by
  let K := RationalCoefficients F
  let v : AddValuation K (WithTop ℤ) := rationalValuation F
  let ζ : K := callPoint F cap j
  have h₂ : v 2 = 1 := rationalValuation_two F
  have hζ : 0 ≤ v ζ := rationalValuation_integer F _
  change 0 ≤ v (rowLinearAt F G cap t j X x)
  unfold rowLinearAt
  apply S7.valuation_sum_bound v
  intro y _
  rw [v.map_mul]
  apply add_nonneg _ (S7.valuation_nat_nonnegative v _)
  unfold kernel
  split
  · have h := eval_bound v (kernel_integral_shift v h₂ (G.packing.position x).2
        (G.packing.position y).2 (active_mem_grid t)) hζ
    simpa only [eval_comp,eval_add,eval_C,eval_mul,eval_X,nodeProbe] using h
  · simp

def integralPhysicalTerm (bits : SampleBits F G t) : integralElements F :=
  let pair := (splitPortsEquiv c.network G.left G.right (G.coord t)).symm bits
  let old := c.network.rowProduct pair.1 * c.network.colProduct pair.2
  ⟨integerRational F.f old,rationalValuation_integer F old⟩ *
    ∏ x,
      let row : integralElements F := ⟨rowLinearAt F G cap t j pair.2 x,
        rowLinearAt_integral F G cap t j pair.2 x⟩
      if pair.1 x then row else 1-row

theorem integralPhysicalTerm_coe (bits : SampleBits F G t) :
    (integralPhysicalTerm F G cap t j bits).val = physicalSampleTerm F G cap t j bits := by
  change (integralElements F).subtype (integralPhysicalTerm F G cap t j bits) = _
  unfold integralPhysicalTerm physicalSampleTerm
  dsimp only
  rw [map_mul,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  split
  · rfl
  · rfl

theorem exactCallProbe_integral :
    exactCallProbe F G cap t j =
      (∑ bits : SampleBits F G t, integralPhysicalTerm F G cap t j bits : integralElements F).val := by
  rw [exactCallProbe_physical]
  change _ = (integralElements F).subtype (∑ bits, integralPhysicalTerm F G cap t j bits)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro bits _
  exact (integralPhysicalTerm_coe F G cap t j bits).symm

/-- A proof-level expansion, over the genuine bit strings. The running
    solver uses the mode DFS and obtains each child recursively. -/
theorem exactCallProbe_reduce :
    tryWord F.monic (callPrecision s c t.val) (exactCallProbe F G cap t j) =
      some (∑ bits : SampleBits F G t,
        reduceElements F (callPrecision s c t.val) (integralPhysicalTerm F G cap t j bits)) := by
  rw [exactCallProbe_integral]
  rw [reduceElements_spec,map_sum]

end RootSeparation.Solver

#print axioms RootSeparation.Solver.rowLinearAt_integral
#print axioms RootSeparation.Solver.exactCallProbe_reduce
