import P5MainBalanceM6SourceMain
import P5MainBalanceM6TailActual

/-! All numerical measurements and geometry-to-thinning margins are
now supplied from the actual schedule itself. No external row
concentration premise remains; the legal graph-only cap and the
correct compiled source inputs remain as the actual mathematical input. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Filter Real Polynomial
open scoped BigOperators Classical

universe u v w x y
set_option maxHeartbeats 7500000 in
theorem eventual_printed_M6_without_tail
    (a C b : ℕ) (ha : 0<a) (hC : 0<C) (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {V : Type u} {W : Type v} {E : Type w} {F : Type x} {Copy : Type y}
        [Fintype V] [DecidableEq V] [Nonempty V]
        [Fintype W] [Nonempty W] [Fintype E] [Fintype F] [Fintype Copy],
      ∀ (graph : Finset (V×V))
        (L : SourceLayout E W F Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)))
        (mark : V↪E)
        (P : SourceRecipe L mark) (base : F→ℕ) (slope ell : ℕ),
      let M : Mix Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)) := printedMix (printedStart n) (mainWidth 1 n)
      let d := (∑ f,base f)+slope*(ell-1)
      let D := Fintype.card (WordCell (Fin (mainNodes n)) (Fin (mainAlphabet n)))
      Fintype.card W=n →
      Fintype.card V≤n → n≤a*Fintype.card V →
      2*Fintype.card E≤C*Fintype.card V →
      (∀ u,cellLoad L u*D≤2*Fintype.card E) →
      Fintype.card Copy*D≤2*Fintype.card E →
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
  obtain ⟨ε,he,hEvent⟩ := eventual_printed_M6 a C b ha hC γ hγ hγ1
  refine ⟨ε,he,?_⟩
  filter_upwards [hEvent,eventual_printed_actual_tail] with n hn hTail
  intro V W E F Copy _ _ _ _ _ _ _ _ graph L mark P base slope ell
  dsimp only
  intro hW hN hRa hm hCps hCopies hLoop hReg hExp hGrade hD hEll out hOut hParity
  exact hn graph L mark P base slope ell hW hN hRa hm hCps hCopies hTail
    hLoop hReg hExp hGrade hD hEll out hOut hParity

#print axioms eventual_printed_M6_without_tail
end P5MainBalance.M6
