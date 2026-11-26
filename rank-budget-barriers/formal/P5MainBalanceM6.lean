import P5MainBalanceM5
import P5MainBalanceHighOrder

/-! Finite M.6 transfer. The low-order budget is the exact number
of source Taylor pairs times true measurement tuples times the actual
double-truncation dimension. Its verification for an implementation is
kept separate from the terminal high-order conclusion. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Real Polynomial

variable {V W I B P : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype B] [DecidableEq B] [Nonempty B] [Fintype P]
  {graph : Finset (V×V)} {mark : V↪P} {cell : P→(I→B) × (I→B)} {C : ℕ}

set_option maxHeartbeats 10500000 in
theorem native_M6_from_literal_low_budget (L : MainIncidence.Layout graph mark cell C)
    (hsize : 7776*(Fintype.card I:ℚ)*(4*C*(Fintype.card I:ℚ))/
      (FiniteGrowth.coefficient L.gamma (1/4))^2 < Fintype.card V)
    (t : I→ℚ) (ht : Function.Injective t) (k : I→ℕ) (ell : ℕ)
    (H : (V→Bool)→Bivariate) (hdeg : ∀ σ,(H σ).degree<↑(∑ i,k i))
    (out : (V→Bool)→ℤ)
    (hOut : ∀ σ,(out σ:ℚ)=retainedOrigin ell (H σ))
    (hParity : ∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2))
    (Y : I→ℕ) (a : ℕ) (ε : ℝ) (hε : 0≤ε)
    (hQ : 2≤Fintype.card I) (hVars : Fintype.card W≤a*Fintype.card V)
    (hFast : 2*(a:ℝ)≤ε*sqrt (Fintype.card I:ℝ))
    (hMisc : ∀ i : I, ∀ j : ℕ,
        (j:ℝ)*log (2*(Fintype.card I:ℝ))≤ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) →
        ((Y i*ell*(j+1):ℕ):ℝ)≤exp (ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)))
    (hLocal : ∀ u : JetIndex k × Fin ell,
        (u.1.2.val:ℝ)*log (2*(Fintype.card I:ℝ))≤ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) →
        cutLength (EmpiricalCutMoments.labelCut (MainIncidence.labels mark cell) id L.symbols u.1.1)
          (fun σ => nativeCoeff (H σ) (t u.1.1) u.1.2 u.2) ≤
        (P5MainIterator.TaylorList W u.1.2).card * Y u.1.1 * (ell*(u.1.2.val+1)))
    (hRoom : ∀ d : ℕ, (FiniteGrowth.coefficient L.gamma (1/4)*Fintype.card V)^2≤
      16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 →
      3*ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) ≤ ((d/2:ℕ):ℝ)*log 2 ∧
      Fintype.card (JetIndex k × Fin ell) < 2^(d-d/2)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient L.gamma (1/4)*Fintype.card V)^2≤
      16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 ∧
      ∃ u : JetIndex k × Fin ell,
        ε*(Fintype.card V:ℝ)/(sqrt (Fintype.card I:ℝ)*log (2*(Fintype.card I:ℝ))) <
          (u.1.2.val:ℝ) ∧
        2^(d/2) < cutLength (EmpiricalCutMoments.labelCut
          (MainIncidence.labels mark cell) id L.symbols u.1.1)
          (fun σ => nativeCoeff (H σ) (t u.1.1) u.1.2 u.2) := by
  let N := Fintype.card V
  let Q := Fintype.card I
  let p := ε*(N:ℝ)/(sqrt (Q:ℝ)*log (2*(Q:ℝ)))
  let q₀ := ⌊p⌋₊
  have hN : 0<N := Fintype.card_pos
  have hQ' : 0<(Q:ℝ) := by exact_mod_cast (by omega : 0<Q)
  have hlog : 0<log (2*(Q:ℝ)) := by
    apply log_pos
    have h : (2:ℝ)≤Q := by exact_mod_cast hQ
    linarith only [h]
  have hp : 0≤p := by dsimp [p]; exact div_nonneg (by positivity) (by positivity)
  let rank (u : JetIndex k × Fin ell) :=
    cutLength (EmpiricalCutMoments.labelCut (MainIncidence.labels mark cell) id L.symbols u.1.1)
      (fun σ=>nativeCoeff (H σ) (t u.1.1) u.1.2 u.2)
  obtain ⟨d,hd,hBudget⟩ := native_M5 L hsize t ht k ell H hdeg out hOut hParity
  have hR := hRoom d hd
  have hSmall (u : JetIndex k × Fin ell) (hu : u.1.2.val≤q₀) : rank u≤2^(d/2) := by
    have hJ : (u.1.2.val:ℝ)≤(q₀:ℝ) := by exact_mod_cast hu
    have h₁ : (u.1.2.val:ℝ)≤p := hJ.trans (Nat.floor_le hp)
    have h₂ : (u.1.2.val:ℝ)*log (2*(Q:ℝ))≤ε*(N:ℝ)/sqrt (Q:ℝ) := by
      have h := mul_le_mul_of_nonneg_right h₁ hlog.le
      dsimp [p] at h
      convert h using 1
      field_simp [hlog.ne',(sqrt_pos.2 hQ').ne']
    have H := combining_low_costs (W:=W) u.1.2 Q N a (Y u.1.1) ell ε
      hQ hN hε hVars hFast h₂ (hMisc _ _ h₂)
    have hc : (rank u:ℝ)≤
        ((P5MainIterator.TaylorList W u.1.2).card * Y u.1.1 * (ell*(u.1.2.val+1)):ℕ) := by
      exact_mod_cast hLocal u h₂
    have hPow : exp (((d/2:ℕ):ℝ)*log 2)=(2^(d/2):ℕ) := by
      rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
      push_cast
      rfl
    have hexp := exp_le_exp.mpr hR.1
    rw [hPow] at hexp
    exact_mod_cast (hc.trans (H.trans hexp))
  obtain ⟨u,hu,hr⟩ := high_order_after_low_exclusion (fun u : JetIndex k × Fin ell=>u.1.2.val)
    rank d q₀ hBudget hR.2 hSmall
  refine ⟨d,hd,u,?_,hr⟩
  have hf : (q₀:ℝ)+1≤(u.1.2.val:ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hu
  exact (Nat.lt_floor_add_one p).trans_le hf

#print axioms native_M6_from_literal_low_budget
end P5MainBalance
