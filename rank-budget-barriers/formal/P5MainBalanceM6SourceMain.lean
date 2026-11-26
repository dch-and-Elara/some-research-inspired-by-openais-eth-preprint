import P5MainBalanceM6Published
import P5MainBalanceM6SourceBase
import P5MainBalanceM6Band
import P5MainBalanceM6RowDegree

/-! Current source-facing M.6. This is the *actual* V₀f(W₀) row array
and its node-dependent exact branches, with one common physical chart.
It does not claim that arbitrary Recipe data is correct for a CNF:
the original final-integer/parity correctness and the separate
concentration/geometry certificates remain explicit. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Filter Real Polynomial
open scoped BigOperators Classical

variable {E W F Copy I B : Type*} [Fintype E] [Fintype W]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

theorem actual_printed_row_grade (L : SourceLayout E W F Copy I B) (t : I→ℚ) (A R : ℕ)
    (e : E) (x : W→ℚ) :
    (physicalRow L t (printedMix A R) e x).natDegree≤R-1 :=
  physicalRow_degree_from_support L t (printedMix A R) (R-1)
    (printed_mix_mismatch A R) e x

universe u v w x y
set_option maxHeartbeats 7500000 in
theorem eventual_printed_M6
    (a C b : ℕ) (ha : 0<a) (hC : 0<C) (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {V : Type u} {W : Type v} {E : Type w} {F : Type x} {Copy : Type y}
        [Fintype V] [DecidableEq V] [Nonempty V]
        [Fintype W] [Nonempty W] [Fintype E] [Fintype F] [Fintype Copy],
      ∀ (graph : Finset (V×V))
        (L : SourceLayout E W F Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)))
        (mark : V↪E)
        (P : SourceRecipe L mark) (base : F→ℕ) (slope ell : ℕ),
      let keep := outsideInterval (printedStart n) (mainWidth 1 n)
      let M : Mix Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)) := printedMix (printedStart n) (mainWidth 1 n)
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
  obtain ⟨ε,he,hEvent⟩ := eventual_physical_M6_from_source_certificates a C b ha hC γ hγ hγ1
  refine ⟨ε,he,?_⟩
  filter_upwards [hEvent] with n hn
  intro V W E F Copy _ _ _ _ _ _ _ _ graph L mark P base slope ell
  dsimp only
  intro hW hN hRa hm hCps hCopies hTail hLoop hReg hExp hGrade hD hEll out hOut hParity
  let A := printedStart n
  let R := mainWidth 1 n
  let M : Mix Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)) := printedMix A R
  let keep := outsideInterval A R
  have hInv : ActualBaseInvariant keep L M := printed_source_base_invariant L A R
  have hRow (e : E) (x : W→Bool) :
      (physicalRow L (nativeGrid n) M e (qbits x)).natDegree≤R :=
    (actual_printed_row_grade L (nativeGrid n) A R e (qbits x)).trans (Nat.sub_le _ _)
  exact hn graph L mark keep M P base slope ell hW hN hRa hm hCps hCopies hTail
    hLoop hReg hExp hInv hRow hGrade hD hEll out hOut hParity

#print axioms actual_printed_row_grade
#print axioms eventual_printed_M6
end P5MainBalance.M6
