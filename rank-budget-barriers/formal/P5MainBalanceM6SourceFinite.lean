import P5MainBalanceM6Finite
import P5MainBalanceM6SourceBase
import P5MainBalanceM6Band
import P5MainBalanceM6RowDegree
import P5MainBalanceM6ExactBox
import P5MainBalanceM6Grade

/-! One finite theorem for the actual printed row action, exact D-box,
source grading and original coherent coefficients. Unlike the generic
finite M.6 transport, this result has no caller-supplied measurement,
local-rank or deformation-degree premise. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial Real
open scoped BigOperators Classical

variable {E W F Copy I B V : Type*} [Fintype E] [Fintype W] [Nonempty W]
  [Fintype F] [Fintype Copy] [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype B] [LinearOrder B] [Nonempty B]
  [Fintype V] [DecidableEq V] [Nonempty V]

set_option maxHeartbeats 16000000 in
theorem finite_printed_row_M6
    (L : SourceLayout E W F Copy I B) (mark : V↪E) (graph : Finset (V×V)) (C : ℕ)
    (G : MainIncidence.Layout graph mark (realCell L) C)
    (hsize : 7776*(Fintype.card I:ℚ)*(4*C*(Fintype.card I:ℚ))/
      (FiniteGrowth.coefficient G.gamma (1/4))^2 < Fintype.card V)
    (t : I→ℚ) (ht : Function.Injective t) (ht0 : ∀ i,t i≠0)
    (A R : ℕ) (k : I→ℕ) (ell : ℕ) (P : SourceRecipe L mark)
    (base : F→ℕ) (slope : ℕ) (hGrade : P.graded base slope)
    (hTotal : ((∑ f,base f)+slope*(ell-1))*R<∑ i,k i)
    (out : (V→Bool)→ℤ)
    (hOut : ∀ σ,(out σ:ℚ)=retainedOrigin ell (actualH L mark t (printedMix A R) P σ))
    (hParity : ∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2))
    (a : ℕ) (ε : ℝ) (hε : 0≤ε)
    (hQ : 2≤Fintype.card I) (hVars : Fintype.card W≤a*Fintype.card V)
    (hFast : 2*(a:ℝ)≤ε*sqrt (Fintype.card I:ℝ))
    (hBox : ∀ j : ℕ,
        (j:ℝ)*log (2*(Fintype.card I:ℝ))≤ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) →
        ((exactBox (outsideInterval A R) L*ell*(j+1):ℕ):ℝ)≤
          exp (ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)))
    (hRoom : ∀ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4)*Fintype.card V)^2≤
      16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 →
      3*ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) ≤ ((d/2:ℕ):ℝ)*log 2 ∧
      Fintype.card (JetIndex k × Fin ell) < 2^(d-d/2)) :
    HighWitness L mark C G.gamma G.symbols t k ell
      (fun σ=>trimV ell (actualH L mark t (printedMix A R) P σ)) ε := by
  let keep := outsideInterval A R
  let M : Mix Copy I B := printedMix A R
  have hBase : ActualBaseInvariant keep L M := printed_source_base_invariant L A R
  have hR (e : E) (x : W→Bool) : (physicalRow L t M e (qbits x)).natDegree≤R :=
    (physicalRow_degree_from_support L t M (R-1) (printed_mix_mismatch A R) e (qbits x)).trans
      (Nat.sub_le _ _)
  have hGradeRoom : (∑ f,base f)*R+(slope*R)*(ell-1)<∑ i,k i := by
    have hr : (∑ f,base f)*R+(slope*R)*(ell-1)=((∑ f,base f)+slope*(ell-1))*R := by ring
    rwa [hr]
  have hSlice (σ : V→Bool) (s : Fin ell) :
      (vSlice s (actualH L mark t M P σ)).degree<↑(∑ i,k i) :=
    retained_bigrade_bound _ (actualH_bigrade L mark t M R hR P base slope hGrade σ)
      hGradeRoom s
  exact finite_actual_M6 keep L mark graph C G hsize t ht ht0 k ell M hBase P hSlice out hOut hParity
    a ε hε hQ hVars hFast (exactBox keep L) (actualY_card_in_D_box keep L) hBox hRoom

#print axioms finite_printed_row_M6
end P5MainBalance.M6
