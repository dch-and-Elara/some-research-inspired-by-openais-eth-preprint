import P5MainBalanceM6SourceFinite
import P5MainBalanceM6SourceMain
import P5MainBalanceTerminal
import P5AlwaysSatOriginalPhysicalCNF

/-! Finite M.4–M.6 for an actual typed source recipe once the literal
origin and grade have been established. No rank or coefficient correctness
is a hypothesis. The finite graph and parameter margins remain visible. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6 Polynomial Real
open scoped BigOperators Classical Polynomial

variable {V X W F Copy I B : Type*}
  [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype X] [Fintype W] [Nonempty W] [Fintype F] [Fintype Copy]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype B] [LinearOrder B] [Nonempty B]

variable {E : Finset (V×V)} {T : Finset V}

def FiniteSize {L : SourceLayout X W F Copy I B} {mark : V↪X} {C : ℕ}
    (G : MainIncidence.Layout E mark (realCell L) C) : Prop :=
  7776*(Fintype.card I:ℚ)*(4*C*(Fintype.card I:ℚ))/
    (FiniteGrowth.coefficient G.gamma (1/4))^2 < Fintype.card V

def M5Witness (L : SourceLayout X W F Copy I B) (mark : V↪X)
    (C : ℕ) (γ : ℚ) (S : I→Finset B) (t : I→ℚ) (k : I→ℕ) (ell : ℕ)
    (H : (V→Bool)→Bivariate) : Prop :=
  ∃ d : ℕ, (FiniteGrowth.coefficient γ (1/4)*Fintype.card V)^2≤
    16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 ∧
    2^d≤∑ a : JetIndex k × Fin ell,
      cutLength (EmpiricalCutMoments.labelCut (MainIncidence.labels mark (realCell L)) id S a.1.1)
        (fun σ=>nativeCoeff (H σ) (t a.1.1) a.1.2 a.2)

set_option maxHeartbeats 5000000 in
omit [Nonempty W] in
theorem finite_source_M5 (L : SourceLayout X W F Copy I B) (mark : V↪X) (C : ℕ)
    (G : MainIncidence.Layout E mark (realCell L) C) (hS : FiniteSize G)
    (t : I→ℚ) (ht : Function.Injective t) (A R : ℕ) (k : I→ℕ) (ell : ℕ)
    (P : SourceRecipe L mark) (base : F→ℕ) (slope : ℕ)
    (hGrade : P.graded base slope)
    (hTotal : ((∑ f, base f)+slope*(ell-1))*R<∑ i,k i)
    (out : (V→Bool)→ℤ)
    (hOut : ∀ σ,(out σ:ℚ)=retainedOrigin ell (actualH L mark t (printedMix A R) P σ))
    (hParity : ∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula E σ):ZMod 2)) :
    M5Witness L mark C G.gamma G.symbols t k ell
      (fun σ=>trimV ell (actualH L mark t (printedMix A R) P σ)) := by
  let M : Mix Copy I B := printedMix A R
  have hRow (e : X) (x : W→Bool) :
      (physicalRow L t M e (qbits x)).natDegree≤R :=
    (actual_printed_row_grade L t A R e (qbits x)).trans (Nat.sub_le _ _)
  have hRun : (∑ f,base f)*R+(slope*R)*(ell-1)<∑ i,k i := by
    have hh : (∑ f,base f)*R+(slope*R)*(ell-1)=((∑ f,base f)+slope*(ell-1))*R := by ring
    rw [hh]
    exact hTotal
  have hD (σ : V→Bool) :
    (trimV ell (actualH L mark t M P σ)).degree < ↑(∑ i,k i) := by
    apply (trimmed_degree_iff ell _ _).mpr
    exact retained_bigrade_bound _
      (actualH_bigrade L mark t M R hRow P base slope hGrade σ) hRun
  exact native_M5 G hS t ht k ell _ hD out
    (fun σ => (hOut σ).trans (retained_origin_trim ell _).symm) hParity

def FiniteMargins (L : SourceLayout X W F Copy I B) (mark : V↪X) (C : ℕ)
    (G : MainIncidence.Layout E mark (realCell L) C)
    (A R : ℕ) (k : I→ℕ) (ell : ℕ) (ε : ℝ) : Prop :=
  FiniteSize G ∧ 0≤ε ∧ 2≤Fintype.card I ∧
    (18:ℝ)≤ε*sqrt (Fintype.card I:ℝ) ∧
    (∀ j : ℕ,
      (j:ℝ)*log (2*(Fintype.card I:ℝ))≤ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) →
      ((exactBox (outsideInterval A R) L*ell*(j+1):ℕ):ℝ)≤
        exp (ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ))) ∧
    (∀ d : ℕ,(FiniteGrowth.coefficient G.gamma (1/4)*Fintype.card V)^2≤
      16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 →
      3*ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)≤((d/2:ℕ):ℝ)*log 2 ∧
      Fintype.card (JetIndex k × Fin ell) < 2^(d-d/2))

set_option maxHeartbeats 5000000 in
theorem finite_source_both (L : SourceLayout X W F Copy I B) (mark : V↪X) (C : ℕ)
    (G : MainIncidence.Layout E mark (realCell L) C)
    (t : I→ℚ) (ht : Function.Injective t) (ht0 : ∀ i,t i≠0)
    (A R : ℕ) (k : I→ℕ) (ell : ℕ) (ε : ℝ)
    (P : SourceRecipe L mark) (base : F→ℕ) (slope : ℕ) (hGrade : P.graded base slope)
    (hTotal : ((∑ f,base f)+slope*(ell-1))*R<∑ i,k i)
    (margin : FiniteMargins L mark C G A R k ell ε) (hW : Fintype.card W≤9*Fintype.card V)
    (out : (V→Bool)→ℤ)
    (hOut : ∀ σ,(out σ:ℚ)=retainedOrigin ell (actualH L mark t (printedMix A R) P σ))
    (hParity : ∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula E σ):ZMod 2)) :
    M5Witness L mark C G.gamma G.symbols t k ell
        (fun σ=>trimV ell (actualH L mark t (printedMix A R) P σ)) ∧
      HighWitness L mark C G.gamma G.symbols t k ell
        (fun σ=>trimV ell (actualH L mark t (printedMix A R) P σ)) ε := by
  rcases margin with ⟨hS,hε,hQ,hFast,hBox,hRoom⟩
  refine ⟨finite_source_M5 L mark C G hS t ht A R k ell P base slope hGrade hTotal out hOut hParity,?_⟩
  exact finite_printed_row_M6 L mark E C G hS t ht ht0 A R k ell P base slope hGrade
    hTotal out hOut hParity 9 ε hε hQ hW (by exact_mod_cast hFast) hBox hRoom

omit [Fintype W] [Nonempty W] [Fintype F] [Fintype Copy] in
theorem finite_actual_output_M4 {L : SourceLayout X W F Copy I B} {mark : V↪X}
    {C : ℕ} (G : MainIncidence.Layout E mark (realCell L) C) (hS : FiniteSize G)
    {Terms : Type*} [Fintype Terms] (out : (V→Bool)→ℤ)
    (pieces : Terms→GroupProducts.GroupTerm (MainIncidence.labels mark (realCell L)) ℚ)
    (hRep : ∀ σ,(out σ:ℚ)=∑ q,(pieces q).value σ)
    (hMod : ∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (cloneCNF E T σ):ZMod 2)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4)*Fintype.card V)^2≤
      16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 ∧ 2^d≤Fintype.card Terms := by
  apply MainIncidence.main_modular_group_barrier G hS (Int.castRingHom ℚ)
    (Int.castRingHom (ZMod 2)) Int.cast_injective out pieces hRep
  intro σ
  change (out σ:ZMod 2)=_
  rw [hMod σ,← ZMod.natCast_mod (PinnedCNF.modelCount (cloneCNF E T σ)) 2,cloned_count_parity]

omit [Fintype W] [Nonempty W] [Fintype F] [Fintype Copy] in
theorem finite_actual_weighted_M4 {L : SourceLayout X W F Copy I B} {mark : V↪X}
    {C : ℕ} (G : MainIncidence.Layout E mark (realCell L) C) (hS : FiniteSize G)
    {Terms : Type*} [Fintype Terms] (out : (V→Bool)→ℤ)
    (K : Terms→(V→Bool)→ℚ) (nodes : Terms→I) (weight : Terms→ℚ) (budget : Terms→ℕ)
    (hRep : ∀ σ,(out σ:ℚ)=∑ a,weight a*K a σ)
    (hMod : ∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (cloneCNF E T σ):ZMod 2))
    (hLocal : ∀ a,cutLength
      (EmpiricalCutMoments.labelCut (MainIncidence.labels mark (realCell L)) id G.symbols (nodes a))
      (K a) ≤ budget a) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4)*Fintype.card V)^2≤
      16*(C:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 ∧ 2^d≤∑ a,budget a := by
  have hm (σ : V→Bool) : (Int.castRingHom (ZMod 2)) (out σ)=
      (PinnedCNF.modelCount (PinnedCNF.formula E σ):ZMod 2) := by
    change (out σ:ZMod 2)=_
    rw [hMod σ,← ZMod.natCast_mod (PinnedCNF.modelCount (cloneCNF E T σ)) 2,cloned_count_parity]
  obtain ⟨d,hd,hh⟩ := fixed_readout_coefficient_budget G hS (Int.castRingHom ℚ)
    (Int.castRingHom (ZMod 2)) Int.cast_injective out K nodes weight hRep hm
  exact ⟨d,hd,hh.trans (Finset.sum_le_sum (fun a _=>hLocal a))⟩

#print axioms finite_actual_weighted_M4
#print axioms finite_actual_output_M4
#print axioms finite_source_M5
#print axioms finite_source_both
end Paper5.AlwaysSatOriginal.Physical.Taylor