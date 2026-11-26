import SolverParentWords

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial Classical
open scoped BigOperators

variable {s : ℕ} (F : SourcePolynomial (4*lambda s))
variable {c : Call F.f} (G : CallLayout s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^(4*lambda s))
variable (t : callCenters s c) (j : callProbes s c)

def exactKernelEntry (x y : c.network.Wire) : RationalCoefficients F :=
  (kernel G.packing.position x y).eval (nodeProbe t (callPoint F cap j))

theorem exactKernelEntry_integral (x y : c.network.Wire) :
    0 ≤ rationalValuation F (exactKernelEntry F G cap t j x y) := by
  let v : AddValuation (RationalCoefficients F) (WithTop ℤ) := rationalValuation F
  change 0 ≤ v ((kernel (K := RationalCoefficients F) G.packing.position x y).eval
    (nodeProbe t (callPoint F cap j)))
  unfold kernel
  split
  · have h := eval_bound v
      (kernel_integral_shift (K := RationalCoefficients F) _ (rationalValuation_two F)
        (G.packing.position x).2 (G.packing.position y).2 (active_mem_grid t))
      (rationalValuation_integer F (callBinary F cap j))
    simpa only [eval_comp,eval_add,eval_C,eval_mul,eval_X,nodeProbe] using h
  · simp

def expandedKernelEntry (x y : c.network.Wire) : RationalCoefficients F :=
  if (G.packing.position x).1 = (G.packing.position y).1 ∧
    (G.packing.cell x).1 (G.coord t) ≠ (G.packing.cell y).2 (G.coord t) then
      realCrossingSeries F G t cap j x y
  else exactKernelEntry F G cap t j x y

theorem exact_expandedKernel_residue (x y : c.network.Wire) :
    tryWord F.monic (callPrecision s c t.val) (exactKernelEntry F G cap t j x y) =
      tryWord F.monic (callPrecision s c t.val) (expandedKernelEntry F G cap t j x y) := by
  unfold expandedKernelEntry
  split
  · rename_i h
    have he : exactKernelEntry F G cap t j x y = realKernelAt F G t cap j x y := by
      unfold exactKernelEntry realKernelAt kernel
      rw [if_pos h.1]
    rw [he]
    exact realCrossingSeries_residue F G t cap j x y h.1 h.2
  · rfl

theorem expandedKernelEntry_integral (x y : c.network.Wire) :
    0 ≤ rationalValuation F (expandedKernelEntry F G cap t j x y) := by
  have h := reduceElements_spec F (callPrecision s c t.val)
    ⟨exactKernelEntry F G cap t j x y, exactKernelEntry_integral F G cap t j x y⟩
  rw [exact_expandedKernel_residue F G cap t j x y] at h
  apply (coordinateOrder_nonnegative F.monic F.degree _).2
  by_contra hn
  unfold tryWord at h
  rw [dif_neg hn] at h
  cases h

def expandedRow (X : c.network.Wire → Bool) (x : c.network.Wire) : integralElements F :=
  ∑ y : c.network.Wire,
    ⟨expandedKernelEntry F G cap t j x y,expandedKernelEntry_integral F G cap t j x y⟩ *
      (X y).toNat

/-- Substituting the printed geometric series simultaneously for every
crossing column of an actual row preserves that row's word residue. -/
theorem rowLinearAt_residue (X : c.network.Wire → Bool) (x : c.network.Wire) :
    tryWord F.monic (callPrecision s c t.val) (rowLinearAt F G cap t j X x) =
      some (reduceElements F (callPrecision s c t.val) (expandedRow F G cap t j X x)) := by
  let p := callPrecision s c t.val
  let exact (y : c.network.Wire) : integralElements F :=
    ⟨exactKernelEntry F G cap t j x y,exactKernelEntry_integral F G cap t j x y⟩
  let expanded (y : c.network.Wire) : integralElements F :=
    ⟨expandedKernelEntry F G cap t j x y,expandedKernelEntry_integral F G cap t j x y⟩
  have hr : rowLinearAt F G cap t j X x = (∑ y, exact y * (X y).toNat).val := by
    change _ = (integralElements F).subtype (∑ y, exact y * (X y).toNat)
    simp only [map_sum,map_mul,map_natCast]
    rfl
  rw [hr,reduceElements_spec]
  congr 1
  unfold expandedRow
  simp only [map_sum,map_mul,map_natCast]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  have hX := reduceElements_spec F p (exact y)
  have hY := reduceElements_spec F p (expanded y)
  have e := exact_expandedKernel_residue F G cap t j x y
  change tryWord F.monic p (exact y).val = tryWord F.monic p (expanded y).val at e
  rw [hX,hY,Option.some.injEq] at e
  exact e

end RootSeparation.Solver

#print axioms RootSeparation.Solver.exact_expandedKernel_residue
#print axioms RootSeparation.Solver.rowLinearAt_residue
