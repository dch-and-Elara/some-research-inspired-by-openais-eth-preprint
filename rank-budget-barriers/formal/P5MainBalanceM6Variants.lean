import P5MainBalanceM6NoTail
import P5MainBalanceM6SparseTerminal
import P5MainBalanceM6DirectTop

/-! Actual printed-parameter corollaries for the three separately
compiled source families. Each uses its genuine nominal Hermite order.
No source recipe, exact count/parity or concentration binder remains.
Graph-only admissible placements and fixed cubic graph expansion are
the retained mathematical hypotheses. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial Real Filter
open scoped BigOperators Classical

universe u v w a b
variable {V : Type u} {W : Type w} {E : Type a} {F : Type b} {Copy : Type v}

structure PrintedCaps (n : ℕ) (graph : Finset (V×V))
    [Fintype V] [DecidableEq V] [Fintype E] [Fintype Copy]
    (L : SourceLayout E W F Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)))
    (γ : ℚ) : Prop where
  cell : ∀ u,cellLoad L u*Fintype.card (WordCell (Fin (mainNodes n)) (Fin (mainAlphabet n)))≤
    2*Fintype.card E
  copies : Fintype.card Copy*Fintype.card (WordCell (Fin (mainNodes n)) (Fin (mainAlphabet n)))≤
    2*Fintype.card E
  loopless : ∀ v,(v,v)∉graph
  expansion : ∀ U : Finset V,γ*(min U.card (Fintype.card V-U.card) : ℕ)≤
    ((GraphCutMoments.boundary graph U).card:ℚ)

def PrintedWitness [Fintype V] [DecidableEq V] [Fintype W] [Fintype E] [Fintype F] [Fintype Copy]
    (n C d ell : ℕ) (γ : ℚ) (ε : ℝ)
    (L : SourceLayout E W F Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)))
    (mark : V↪E) (P : SourceRecipe L mark) : Prop :=
  ∃ S : Fin (mainNodes n)→Finset (Fin (mainAlphabet n)),
    (∀ t, (1/4:ℚ)*Fintype.card V≤
      ((min (EmpiricalCutMoments.labelCut (pinWord L mark) id S t).card
        (Fintype.card V-(EmpiricalCutMoments.labelCut (pinWord L mark) id S t).card) : ℕ) : ℚ)) ∧
    HighWitness L mark C γ S (nativeGrid n) (fun _=>printedOrder n d) ell
      (fun σ=>trimV ell (actualH L mark (nativeGrid n) (printedMix (printedStart n) (mainWidth 1 n)) P σ)) ε

set_option maxHeartbeats 16000000 in
theorem eventual_direct_cloned_M6 (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {V : Type u} {Copy : Type v} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype Copy],
      ∀ (graph : Finset (V×V)) (reg : ∀ v,GraphCutMoments.degree graph v=3)
        (L : Direct.Chart (Copy:=Copy) (I:=Fin (mainNodes n)) (B:=Fin (mainAlphabet n)) graph
          (MainClonedCNF.leftSlot graph reg) (MainClonedCNF.rightSlot graph reg)),
      Fintype.card (V×Fin 4)=n → PrintedCaps n graph L.physical γ →
      PrintedWitness n 24 (12*Fintype.card V) 1 γ ε L.physical (MainClonedCNF.pinPort graph)
        (Direct.recipe L) := by
  obtain ⟨ε,he,hevent⟩ := eventual_printed_M6_without_tail 4 24 3 (by decide) (by decide) γ hγ hγ1
  refine ⟨ε,he,?_⟩
  filter_upwards [hevent] with n hn
  intro V Copy _ _ _ _ graph reg L hW hCap
  have hnW := hW
  have hV : Fintype.card V≤n ∧ n≤4*Fintype.card V := by
    rw [Fintype.card_prod,Fintype.card_fin] at hnW
    omega
  have hPorts : 2*Fintype.card (MainClonedCNF.Port graph)≤24*Fintype.card V := by
    rw [MainClonedCNF.port_card graph reg]
    omega
  have hNom : (∑ f : Direct.Factor graph,Direct.width f)+0*(1-1)=12*Fintype.card V := by
    rw [Direct.sum_width_eq_port_card,MainClonedCNF.port_card graph reg,zero_mul,add_zero]
  have hDeg : (∑ f : Direct.Factor graph,Direct.width f)+0*(1-1)≤3*n := by
    rw [hNom]
    rw [Fintype.card_prod,Fintype.card_fin] at hnW
    omega
  have hell : 1≤n+1 := by omega
  let M : Mix Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)) := printedMix (printedStart n) (mainWidth 1 n)
  obtain ⟨out,hOut,hMod⟩ := Direct.direct_terminal_witness L (nativeGrid n) M
  have cert := hn graph L.physical (MainClonedCNF.pinPort graph) (Direct.recipe L) Direct.width 0 1
    hW hV.1 hV.2 hPorts hCap.cell hCap.copies hCap.loopless reg hCap.expansion
    (Direct.graded_literal L) hDeg hell out hOut hMod
  unfold PrintedWitness
  rw [hNom] at cert
  exact cert

#print axioms eventual_direct_cloned_M6

set_option maxHeartbeats 16000000 in
theorem eventual_uncloned_sparse_M6 (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {V : Type u} {Copy : Type v} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype Copy],
      ∀ (graph : Finset (V×V)) (_reg : ∀ v,GraphCutMoments.degree graph v=3)
        (L : Sparse.UChart (Copy:=Copy) (I:=Fin (mainNodes n)) (B:=Fin (mainAlphabet n)) graph),
      Fintype.card V=n → PrintedCaps n graph L.physical γ →
      PrintedWitness n 10 (9*Fintype.card V) (Fintype.card V+1) γ ε L.physical (Sparse.uMark graph)
        ((Sparse.uSource L).compile (Fintype.card V+1)) := by
  obtain ⟨ε,he,hevent⟩ := eventual_printed_M6_without_tail 1 10 9 (by decide) (by decide) γ hγ hγ1
  refine ⟨ε,he,?_⟩
  filter_upwards [hevent] with n hn
  intro V Copy _ _ _ _ graph reg L hW hCap
  have hnW := hW
  have hV : Fintype.card V≤n ∧ n≤1*Fintype.card V := by
    omega
  have hPorts : 2*Fintype.card (Sparse.UPort graph)≤10*Fintype.card V := by
    exact (Sparse.uncloned_nominal_guards graph reg).2.2.2.le
  have hNom : (∑ f : Sparse.UFactor graph,(Sparse.uSource L).base f)+4*((Fintype.card V+1)-1)=9*Fintype.card V := by
    exact Sparse.uncloned_compiled_nominal L reg
  have hDeg : (∑ f : Sparse.UFactor graph,(Sparse.uSource L).base f)+4*((Fintype.card V+1)-1)≤9*n := by
    rw [hNom]
    omega
  have hell : (Fintype.card V+1)≤n+1 := by omega
  let M : Mix Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)) := printedMix (printedStart n) (mainWidth 1 n)
  obtain ⟨out,hOut,hMod⟩ := Sparse.uncloned_compiled_terminal L (Fintype.card V+1) (by omega) (nativeGrid n) M
  have cert := hn graph L.physical (Sparse.uMark graph) ((Sparse.uSource L).compile (Fintype.card V+1)) (Sparse.uSource L).base 4 (Fintype.card V+1)
    hW hV.1 hV.2 hPorts hCap.cell hCap.copies hCap.loopless reg hCap.expansion
    ((Sparse.uSource L).compile_graded (Fintype.card V+1)) hDeg hell out hOut hMod
  unfold PrintedWitness
  rw [hNom] at cert
  exact cert

#print axioms eventual_uncloned_sparse_M6

set_option maxHeartbeats 16000000 in
theorem eventual_cloned_sparse_M6 (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {V : Type u} {Copy : Type v} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype Copy],
      ∀ (graph : Finset (V×V)) (reg : ∀ v,GraphCutMoments.degree graph v=3)
        (L : Sparse.CChart (Copy:=Copy) (I:=Fin (mainNodes n)) (B:=Fin (mainAlphabet n)) graph
          (MainClonedCNF.leftSlot graph reg) (MainClonedCNF.rightSlot graph reg)),
      Fintype.card (V×Fin 4)=n → PrintedCaps n graph L.physical γ →
      PrintedWitness n 32 (29*Fintype.card V) (Fintype.card (V×Fin 4)+1) γ ε L.physical (Sparse.cMark graph)
        ((Sparse.cSource L).compile (Fintype.card (V×Fin 4)+1)) := by
  obtain ⟨ε,he,hevent⟩ := eventual_printed_M6_without_tail 4 32 9 (by decide) (by decide) γ hγ hγ1
  refine ⟨ε,he,?_⟩
  filter_upwards [hevent] with n hn
  intro V Copy _ _ _ _ graph reg L hW hCap
  have hnW := hW
  have hV : Fintype.card V≤n ∧ n≤4*Fintype.card V := by
    rw [Fintype.card_prod,Fintype.card_fin] at hnW
    omega
  have hPorts : 2*Fintype.card (Sparse.CPort graph)≤32*Fintype.card V := by
    exact (Sparse.cloned_nominal_guards graph reg).2.2.2.2.2.le
  have hNom : (∑ f : Sparse.CFactor graph,(Sparse.cSource L).base f)+4*((Fintype.card (V×Fin 4)+1)-1)=29*Fintype.card V := by
    exact Sparse.cloned_compiled_nominal L reg
  have hDeg : (∑ f : Sparse.CFactor graph,(Sparse.cSource L).base f)+4*((Fintype.card (V×Fin 4)+1)-1)≤9*n := by
    rw [hNom]
    rw [Fintype.card_prod,Fintype.card_fin] at hnW
    omega
  have hell : (Fintype.card (V×Fin 4)+1)≤n+1 := by omega
  let M : Mix Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)) := printedMix (printedStart n) (mainWidth 1 n)
  obtain ⟨out,hOut,hMod⟩ := Sparse.cloned_compiled_terminal L (Fintype.card (V×Fin 4)+1) (by omega) (nativeGrid n) M
  have cert := hn graph L.physical (Sparse.cMark graph) ((Sparse.cSource L).compile (Fintype.card (V×Fin 4)+1)) (Sparse.cSource L).base 4 (Fintype.card (V×Fin 4)+1)
    hW hV.1 hV.2 hPorts hCap.cell hCap.copies hCap.loopless reg hCap.expansion
    ((Sparse.cSource L).compile_graded (Fintype.card (V×Fin 4)+1)) hDeg hell out hOut hMod
  unfold PrintedWitness
  rw [hNom] at cert
  exact cert

#print axioms eventual_cloned_sparse_M6

end P5MainBalance.M6
