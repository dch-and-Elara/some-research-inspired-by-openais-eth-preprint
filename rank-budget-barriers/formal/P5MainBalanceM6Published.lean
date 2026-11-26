import P5MainBalanceM6Finite
import P5MainBalanceM6PrintedSchedule
import P5MainBalanceM6Grade
import P5MainBalanceM6PublishedBudget
import P5MainBalanceM6ExactBudget
import P5MainIteratorPrinted

/-! M.6 on every graph-only, capped placement of the original printed
family. Constant density, actual exceptional tail and pointwise source
correctness are explicit. The numerical size margins, the choice of a
balanced sign cut, and the low-order rank cap are derived. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Filter Real Polynomial
open scoped BigOperators Classical

theorem printed_grid_degree_room (n d : ℕ) (hQ : 0<mainNodes n) :
    d*mainWidth 1 n < ∑ _i : Fin (mainNodes n),printedOrder n d := by
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
  unfold printedOrder
  rw [Nat.mul_add,Nat.mul_one]
  let A := d*mainWidth 1 n
  let Q := mainNodes n
  change A<Q*(A/Q)+Q
  calc
    A = A%Q+Q*(A/Q) := (Nat.mod_add_div A Q).symm
    _ = Q*(A/Q)+A%Q := Nat.add_comm _ _
    _ < _ := Nat.add_lt_add_left (Nat.mod_lt _ hQ) _

universe u v w x y
set_option maxHeartbeats 7000000 in
theorem eventual_physical_M6_from_source_certificates
    (a C b : ℕ) (ha : 0<a) (hC : 0<C) (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {V : Type u} {W : Type v} {E : Type w} {F : Type x} {Copy : Type y}
        [Fintype V] [DecidableEq V] [Nonempty V]
        [Fintype W] [Nonempty W] [Fintype E] [Fintype F] [Fintype Copy],
      ∀ (graph : Finset (V×V))
        (L : SourceLayout E W F Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)))
        (mark : V↪E)
        (keep : ℕ→Prop)
        (M : Mix Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)))
        (P : SourceRecipe L mark) (base : F→ℕ) (slope ell : ℕ),
      let d := (∑ f,base f)+slope*(ell-1)
      let D := Fintype.card (WordCell (Fin (mainNodes n)) (Fin (mainAlphabet n)))
      Fintype.card W=n →
      Fintype.card V≤n → n≤a*Fintype.card V →
      2*Fintype.card E≤C*Fintype.card V →
      (∀ u,cellLoad L u*D≤2*Fintype.card E) →
      Fintype.card Copy*D≤2*Fintype.card E →
      (Fintype.card (Exceptional (Unequal (I:=Fin (mainNodes n)) (B:=Fin (mainAlphabet n))) keep):ℝ)
        ≤ (D:ℝ)/(mainLambda n:ℝ)^5 →
      (∀ v,(v,v)∉graph) →
      (∀ v,GraphCutMoments.degree graph v=3) →
      (∀ U : Finset V,γ*(min U.card (Fintype.card V-U.card) : ℕ)≤
          ((GraphCutMoments.boundary graph U).card:ℚ)) →
      ActualBaseInvariant keep L M →
      (∀ e : E,∀ x : W→Bool,(physicalRow L (nativeGrid n) M e (qbits x)).natDegree≤mainWidth 1 n) →
      P.graded base slope →
      d≤b*n → ell≤n+1 →
      ∀ (out : (V→Bool)→ℤ),
        (∀ σ,(out σ:ℚ)=retainedOrigin ell (actualH L mark (nativeGrid n) M P σ)) →
        (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula graph σ):ZMod 2)) →
        ∃ S : Fin (mainNodes n)→Finset (Fin (mainAlphabet n)),
          (∀ t, (1/4:ℚ)*Fintype.card V ≤
            ((min (EmpiricalCutMoments.labelCut (pinWord L mark) id S t).card
              (Fintype.card V-(EmpiricalCutMoments.labelCut (pinWord L mark) id S t).card) : ℕ) : ℚ)) ∧
          HighWitness L mark C γ S (nativeGrid n)
            (fun _=>printedOrder n d) ell
            (fun σ=>trimV ell (actualH L mark (nativeGrid n) M P σ)) ε := by
  let c := exponentConstant γ C
  have hc : 0<c := exponentConstant_pos γ C hγ hC
  let ε := min 1 (c*log 2/9)
  have he : 0<ε := lt_min (by norm_num) (by change 0<c*log 2/9; exact div_pos (mul_pos hc (log_pos (by norm_num))) (by norm_num))
  have hb₁ : ε≤1 := min_le_left _ _
  have hb₂ : 9*ε≤c*log 2 := by
    have H : ε≤c*log 2/9 := min_le_right _ _
    linarith only [H]
  refine ⟨ε,he,?_⟩
  filter_upwards [printed_balance_threshold C,printed_thinning_threshold a C ha γ hγ,
    eventual_exact_numeric_M6 a C 5 ha hC γ hγ ε he hb₁ hb₂,
    eventual_printed_address_count b] with n hAl hTh hNum hAddr
  intro V W E F Copy _ _ _ _ _ _ _ _ graph L mark keep M P base slope ell
  dsimp only
  intro hW hN hRa hPorts hCap hCopies hTail hLoop hReg hExp hM hRowDeg hGrade hD hEll out hOut hParity
  let N := Fintype.card V
  let D := Fintype.card (WordCell (Fin (mainNodes n)) (Fin (mainAlphabet n)))
  let d := (∑ f,base f)+slope*(ell-1)
  let k : Fin (mainNodes n)→ℕ := fun _=>printedOrder n d
  have hMe : Fintype.card E≤C*N := by dsimp [N]; omega
  have hCopy : 1≤Fintype.card Copy := by
    letI : Nonempty Copy := ⟨(L.placement.slot (mark (Classical.choice inferInstance))).1⟩
    exact Fintype.card_pos
  have hDcap : D≤2*Fintype.card E :=
    (by simpa only [one_mul] using Nat.mul_le_mul_right D hCopy :
      D≤Fintype.card Copy*D).trans hCopies
  have hDn : D≤C*n := hDcap.trans (hPorts.trans (Nat.mul_le_mul_left C hN))
  let cB := Fintype.card (Exceptional (Unequal (I:=Fin (mainNodes n)) (B:=Fin (mainAlphabet n))) keep)
  let Y := (2*D+1)^(mainAlphabet n*(Fintype.card Copy*cB))
  have hNumbs := hNum N (Fintype.card E) D (Fintype.card Copy) cB
    ell (Fintype.card ((JetIndex k)×Fin ell))
    hN hRa hMe hCopies hDn hTail hEll (hAddr d ell hD hEll)
  have hQ : 0<mainNodes n := by have := hNumbs.1; omega
  letI : Nonempty (Fin (mainNodes n)) := ⟨⟨0,hQ⟩⟩
  letI : Nonempty (Fin (mainAlphabet n)) :=
    ⟨⟨0,by have := hAl; omega⟩⟩
  let G := layoutFromPhysical L mark graph C hC hPorts hCap
    (by simpa only [Fintype.card_fin] using hAl)
    hLoop hReg γ hγ hγ1 hExp
  refine ⟨G.symbols,?_,?_⟩
  · rw [←signs_own_factor_word]
    exact Classical.choose_spec G.balanced
  · have hSize : 7776*(Fintype.card (Fin (mainNodes n)):ℚ)*
      (4*C*(Fintype.card (Fin (mainNodes n)):ℚ))/(FiniteGrowth.coefficient G.gamma (1/4))^2 <
      Fintype.card V := by
      change 7776*(Fintype.card (Fin (mainNodes n)):ℚ)*
        (4*C*(Fintype.card (Fin (mainNodes n)):ℚ))/(FiniteGrowth.coefficient γ (1/4))^2<N
      rw [Fintype.card_fin]
      exact hTh N hRa
    have hDegree (σ : V→Bool) (s : Fin ell) :
        (vSlice s (actualH L mark (nativeGrid n) M P σ)).degree<↑(∑ i,k i) := by
      have hd := printed_grid_degree_room n d hQ
      have hRun : (∑ f,base f)*mainWidth 1 n+(slope*mainWidth 1 n)*(ell-1)<∑ i,k i := by
        have H : (∑ f,base f)*mainWidth 1 n+(slope*mainWidth 1 n)*(ell-1)=d*mainWidth 1 n := by unfold d; ring
        rw [H]
        exact hd
      exact retained_bigrade_bound _
        (actualH_bigrade L mark (nativeGrid n) M (mainWidth 1 n) hRowDeg P base slope hGrade σ)
        hRun s
    have hQ' : 2≤Fintype.card (Fin (mainNodes n)) := by
      rw [Fintype.card_fin]
      have := hNumbs.1
      omega
    have hYEq : exactBox keep L=Y := by
      unfold Y
      rw [exactBox_eq_copied_rows keep L,Fintype.card_fin (n:=mainAlphabet n)]
      simp only [D,cB,←Nat.card_eq_fintype_card]
    have hActualY : ∀ i, Fintype.card (ActualY keep L i) ≤ Y :=
      fun i => (actualY_card_in_D_box keep L i).trans_eq hYEq
    refine finite_actual_M6 keep L mark graph C G hSize (nativeGrid n) (nativeGrid_inj n)
      (nativeGrid_nonzero n) k ell M hM P hDegree out hOut hParity a ε he.le hQ'
      (hW.trans_le hRa) ?_ Y hActualY ?_ ?_
    · simpa only [Fintype.card_fin] using hNumbs.2.1
    · intro j hj
      rw [Fintype.card_fin] at hj ⊢
      change ((Y*ell*(j+1):ℕ):ℝ)≤exp (ε*(N:ℝ)/sqrt (mainNodes n:ℝ))
      exact hNumbs.2.2.1 j hj
    · intro e he
      change (FiniteGrowth.coefficient γ (1/4)*N)^2 ≤
        16*(C:ℚ)*(Fintype.card (Fin (mainNodes n)):ℚ)*(e:ℚ)^2 at he
      rw [Fintype.card_fin] at he ⊢
      exact hNumbs.2.2.2 e he

#print axioms printed_grid_degree_room
#print axioms eventual_physical_M6_from_source_certificates
end P5MainBalance.M6
