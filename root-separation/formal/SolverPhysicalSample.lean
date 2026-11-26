import SolverPortPartition
import SolverNativeRecovery

noncomputable section
namespace RootSeparation.Solver

open S11 Polynomial Classical
open scoped BigOperators

variable {s : ℕ} (F : SourcePolynomial (4*lambda s))
variable {c : Call F.f} (G : CallLayout s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^(4*lambda s))
variable (t : callCenters s c) (j : callProbes s c)

abbrev SampleBits := (g : Fin 64) → ChildEdge c.network G.left G.right (G.coord t) g → Bool

def rowLinearAt (X : c.network.Wire → Bool) (x : c.network.Wire) : RationalCoefficients F :=
  let T := nodeProbe t (callPoint F cap j)
  ∑ y : c.network.Wire, (kernel G.packing.position x y).eval T * (X y).toNat

def physicalSampleTerm (bits : SampleBits F G t) : RationalCoefficients F :=
  let YX := (splitPortsEquiv c.network G.left G.right (G.coord t)).symm bits
  let Y := YX.1
  let X := YX.2
  let old : RationalCoefficients F := integerRational F.f
    (c.network.rowProduct Y * c.network.colProduct X)
  old * ∏ x, if Y x then rowLinearAt F G cap t j X x else 1 - rowLinearAt F G cap t j X x

/-- The exact parent sample, rewritten using two genuine bits per
physical wire and partitioned into the actual retained-port types. -/
theorem exactCallProbe_physical :
    exactCallProbe F G cap t j = ∑ bits : SampleBits F G t, physicalSampleTerm F G cap t j bits := by
  unfold exactCallProbe
  dsimp only
  rw [callDeformation,normalizedDeformation_center]
  simp only [deformed, eval_finset_sum, eval_mul, eval_C, eval_prod]
  let term (q : (c.network.Wire → Bool) × (c.network.Wire → Bool)) : RationalCoefficients F :=
    let T := nodeProbe t (callPoint F cap j)
    let embed : IntegerRing F.f →+* RationalCoefficients F := integerRational F.f
    let A := c.network.map embed
    A.rowProduct q.2 * A.colProduct q.1 *
      ∏ x, (literalPoly (q.2 x)
        (∑ y, kernel G.packing.position x y * C ((q.1 y).toNat : RationalCoefficients F))).eval T
  change (∑ X, ∑ Y, term (X,Y)) = _
  rw [← Fintype.sum_prod_type term]
  let e := (Equiv.prodComm (c.network.Wire → Bool) (c.network.Wire → Bool)).trans
    (splitPortsEquiv c.network G.left G.right (G.coord t))
  apply Fintype.sum_equiv e
  rintro ⟨X,Y⟩
  have hb : (splitPortsEquiv c.network G.left G.right (G.coord t)).symm (e (X,Y)) = (Y,X) :=
    (splitPortsEquiv c.network G.left G.right (G.coord t)).symm_apply_apply _
  unfold physicalSampleTerm
  dsimp only
  rw [hb]
  change term (X,Y) = _
  unfold term
  dsimp only
  rw [Network.map_rowProduct, Network.map_colProduct, map_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  cases Y x <;>
    simp [literalPoly,rowLinearAt,eval_finset_sum,eval_mul]

end RootSeparation.Solver

#print axioms RootSeparation.Solver.exactCallProbe_physical
