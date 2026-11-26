import P5MainBalanceM6Assembly
import P5MainBalanceM6
import P5MainIteratorBox

/-! The finite original MAIN bridge: the M.6 high-order theorem is
consumed on the same physical Hasse coefficients. The abstract hLocal
binder is discharged by construction, and no constant-size shape
proxy is substituted for a physical source layout. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial Real
open scoped BigOperators Classical

variable {E W F Copy I B V : Type*} [Fintype E] [Fintype W]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def measurementBox (keep : ℕ→Prop) (_L : SourceLayout E W F Copy I B) : ℕ :=
  (2*Fintype.card E+1)^
    (Fintype.card B * Fintype.card (NativeRows keep Copy I B))

theorem actualY_card_le (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I) :
    Fintype.card (ActualY keep L i)≤measurementBox keep L := by
  rw [←Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact actual_attained_upper keep L i

variable [Nonempty W] [Fintype F] [DecidableEq I] [Nonempty I] [Nonempty B]
  [Fintype V] [DecidableEq V] [Nonempty V]

def HighWitness (L : SourceLayout E W F Copy I B) (mark : V↪E)
    (C : ℕ) (γ : ℚ) (S : I→Finset B) (t : I→ℚ) (k : I→ℕ) (ell : ℕ)
    (H : (V→Bool)→Bivariate) (ε : ℝ) : Prop :=
  ∃ d : ℕ, (FiniteGrowth.coefficient γ (1/4)*Fintype.card V)^2≤
    16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 ∧
    ∃ u : JetIndex k × Fin ell,
      ε*(Fintype.card V:ℝ)/(sqrt (Fintype.card I:ℝ)*log (2*(Fintype.card I:ℝ))) <
        (u.1.2.val:ℝ) ∧
      2^(d/2) < cutLength
        (EmpiricalCutMoments.labelCut (MainIncidence.labels mark (realCell L)) id S u.1.1)
        (fun σ=>nativeCoeff (H σ) (t u.1.1) u.1.2 u.2)

set_option maxHeartbeats 16000000 in
theorem finite_actual_M6
    (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (mark : V↪E)
    (graph : Finset (V×V)) (C : ℕ)
    (G : MainIncidence.Layout graph mark (realCell L) C)
    (hsize : 7776*(Fintype.card I:ℚ)*(4*C*(Fintype.card I:ℚ))/
      (FiniteGrowth.coefficient G.gamma (1/4))^2 < Fintype.card V)
    (t : I→ℚ) (ht : Function.Injective t) (ht0 : ∀ i,t i≠0)
    (k : I→ℕ) (ell : ℕ) (M : Mix Copy I B) (hM : ActualBaseInvariant keep L M)
    (P : SourceRecipe L mark)
    (hdeg : ∀ (σ : V→Bool) (s : Fin ell),(vSlice s (actualH L mark t M P σ)).degree<↑(∑ i,k i))
    (out : (V→Bool)→ℤ)
    (hOut : ∀ σ,(out σ:ℚ)=retainedOrigin ell (actualH L mark t M P σ))
    (hParity : ∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2))
    (a : ℕ) (ε : ℝ) (hε : 0≤ε)
    (hQ : 2≤Fintype.card I) (hVars : Fintype.card W≤a*Fintype.card V)
    (hFast : 2*(a:ℝ)≤ε*sqrt (Fintype.card I:ℝ))
    (Ybox : ℕ) (hY : ∀ i : I,Fintype.card (ActualY keep L i)≤Ybox)
    (hBox : ∀ j : ℕ,
        (j:ℝ)*log (2*(Fintype.card I:ℝ))≤ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) →
        ((Ybox*ell*(j+1):ℕ):ℝ)≤exp (ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)))
    (hRoom : ∀ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4)*Fintype.card V)^2≤
      16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 →
      3*ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) ≤ ((d/2:ℕ):ℝ)*log 2 ∧
      Fintype.card (JetIndex k × Fin ell) < 2^(d-d/2)) :
    HighWitness L mark C G.gamma G.symbols t k ell (fun σ=>trimV ell (actualH L mark t M P σ)) ε := by
  exact native_M6_from_literal_low_budget (W:=W) G hsize t ht k ell
    (fun σ=>trimV ell (actualH L mark t M P σ))
    (fun σ=>(trimmed_degree_iff ell _ _).mpr (hdeg σ)) out
    (fun σ => (hOut σ).trans (retained_origin_trim ell _).symm) hParity
    (fun i=>Fintype.card (ActualY keep L i)) a ε hε hQ hVars hFast
    (fun i j hj => by
      apply le_trans _ (hBox j hj)
      exact_mod_cast (Nat.mul_le_mul_right (j+1)
        (Nat.mul_le_mul_right ell (hY i))))
    (fun u _=>actual_native_order_rank_upper keep L mark t M hM P
      G.symbols u.1.1 (ht0 u.1.1) u.1.2 ell u.2) hRoom

#print axioms actualY_card_le
#print axioms finite_actual_M6
end P5MainBalance.M6
