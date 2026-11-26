import P5MainBalanceNative
import P5MainBalanceCutBudget
import Mathlib.Data.ZMod.Basic

/-! M.5 on the literal centered deformation polynomial and its real
retained V slices, not arbitrary callbacks pretending to be Hasse values. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Polynomial

variable {V I B P : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype B] [DecidableEq B] [Nonempty B]
  [Fintype P] {graph : Finset (V×V)} {mark : V↪P} {cell : P→(I→B) × (I→B)} {C : ℕ}

set_option maxHeartbeats 8200000 in
theorem native_M5 (L : MainIncidence.Layout graph mark cell C)
    (hsize : 7776*(Fintype.card I:ℚ)*(4*C*(Fintype.card I:ℚ))/
      (FiniteGrowth.coefficient L.gamma (1/4))^2 < Fintype.card V)
    (t : I→ℚ) (ht : Function.Injective t) (k : I→ℕ) (ell : ℕ)
    (H : (V→Bool)→Bivariate) (hdeg : ∀ σ,(H σ).degree<↑(∑ i,k i))
    (out : (V→Bool)→ℤ)
    (hOut : ∀ σ,(out σ:ℚ)=retainedOrigin ell (H σ))
    (hParity : ∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient L.gamma (1/4)*Fintype.card V)^2≤
      16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 ∧
      2^d≤∑ a : JetIndex k × Fin ell,
        cutLength (EmpiricalCutMoments.labelCut (MainIncidence.labels mark cell) id L.symbols a.1.1)
          (fun σ => nativeCoeff (H σ) (t a.1.1) a.1.2 a.2) := by
  obtain ⟨w,hw⟩ := native_retained_hermite t ht k ell
  exact fixed_readout_coefficient_budget L hsize (Int.castRingHom ℚ) (Int.castRingHom (ZMod 2))
    Int.cast_injective out
    (fun (a : JetIndex k × Fin ell) σ => nativeCoeff (H σ) (t a.1.1) a.1.2 a.2)
    (fun a=>a.1.1) (fun a=>w a.1)
    (fun σ => (hOut σ).trans (hw (H σ) (hdeg σ))) hParity

omit [Nonempty V] [Nonempty B] [Nonempty I] [Fintype I] [DecidableEq I] [Fintype P] in
theorem full_group_lengths_dominate (L : V→I→B) (t : I) (S : I→Finset B)
    (f : (V→Bool)→ℚ) {d : ℕ}
    (terms : Fin d→GroupProducts.GroupTerm L ℚ)
    (hn : ∀ q,(terms q).coordinate=t) (hvalue : ∀ σ,f σ=∑ q,(terms q).value σ) :
    cutLength (EmpiricalCutMoments.labelCut L id S t) f≤d := by
  apply cut_length_minimal
  refine ⟨fun q=>(terms q).toVertexTerm S,?_,?_⟩
  · intro q
    rw [GroupProducts.GroupTerm.toVertexTerm_side,hn q]
  · intro σ
    exact (hvalue σ).trans (GroupProducts.sum_toVertexTerm_values terms S σ).symm

#print axioms native_M5
#print axioms full_group_lengths_dominate
end P5MainBalance
