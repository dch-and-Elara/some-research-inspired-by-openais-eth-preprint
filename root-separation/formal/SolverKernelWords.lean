import SolverPacketWords

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial
open scoped BigOperators

variable {e : ℕ} (F : SourcePolynomial e) {s : ℕ} {c : Call F.f}
variable (G : CallLayout s c) (t : callCenters s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^e)
variable (j : callProbes s c)

def realKernelAt (x y : c.network.Wire) : RationalCoefficients F :=
  eval (R := RationalCoefficients F) (nodeProbe t (callPoint F cap j))
    (packetKernel (RationalCoefficients F) (callL s c) (G.packing.position x).2 (G.packing.position y).2)

def realCrossingSeries (x y : c.network.Wire) : RationalCoefficients F :=
  let K := RationalCoefficients F
  let posx := (G.packing.position x).2
  let posy := (G.packing.position y).2
  let i := level t.val
  let y₀ := posy.val % 2^(i+1)
  let index := posy.val / 2^(i+1)
  let ζ := callPoint F cap j
  let d : K := (((t.val-(y₀:ℕ)+posx.val:ℤ):K) + shiftScale K (callA s c)*ζ)
  let base : K := (shiftedNumerator K (callA s c) t.val).eval ζ / d
  let ratio : K := (2:K)^(i+1) / d
  ∑ b ∈ Finset.range (callPrecision s c t.val - 1), base * ratio^b * (index : K)^b

theorem realCrossingSeries_residue (x y : c.network.Wire)
    (h : (G.packing.position x).1 = (G.packing.position y).1)
    (cross : (G.packing.cell x).1 (G.coord t) ≠ (G.packing.cell y).2 (G.coord t)) :
    tryWord F.monic (callPrecision s c t.val) (realKernelAt F G t cap j x y) =
      tryWord F.monic (callPrecision s c t.val) (realCrossingSeries F G t cap j x y) := by
  let K := RationalCoefficients F
  let v : AddValuation K (WithTop ℤ) := rationalValuation F
  let ζ : K := callPoint F cap j
  let p := callPrecision s c t.val
  let X : K := realKernelAt F G t cap j x y
  let Y : K := realCrossingSeries F G t cap j x y
  have h₂ : v (2:K) = 1 := rationalValuation_two F
  have hζ : 0 ≤ v ζ := rationalValuation_integer F _
  obtain ⟨_,err,he,herr⟩ := crossing_kernel_integral G t v h₂ ζ hζ x y h cross
  have herr' : X-Y = (2:K)^p*err := herr
  have hdiff : (↑(p:ℤ):WithTop ℤ) ≤ v (X-Y) := by
    rw [herr',v.map_mul,val_two_pow v h₂]
    exact le_add_of_nonneg_right he
  have hX : 0 ≤ v X := by
    have hh := eval_bound v (kernel_integral_shift v h₂ (G.packing.position x).2
      (G.packing.position y).2 (active_mem_grid t)) hζ
    simpa only [eval_comp,eval_add,eval_C,eval_mul,eval_X,X,realKernelAt,nodeProbe] using hh
  have hY : 0 ≤ v Y := by
    have h₀ : (0:WithTop ℤ) ≤ (↑(p:ℤ):WithTop ℤ) := by exact_mod_cast (Nat.zero_le p)
    have h := v.map_add X (-(X-Y))
    rw [v.map_neg,neg_sub,show X+(Y-X) = Y by ring] at h
    exact (le_min hX (h₀.trans hdiff)).trans h
  exact tryWord_congr F p (callPrecision_pos s c t.val) X Y hY hdiff

end RootSeparation.Solver

#print axioms RootSeparation.Solver.realCrossingSeries_residue
