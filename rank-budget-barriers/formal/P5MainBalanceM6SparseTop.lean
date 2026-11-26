import P5MainBalanceM6SparseTerminal
import P5MainBalanceM6DirectTop

/-! M.6 for the actual two sparse equation inputs, with all factor,
integrality and mod-2 terminal premises derived. For each branch the
actual cubic incidence/nominal degree determines the Hermite order.
The remaining finite assumptions are the structural and resource ones
of the printed M.6 argument, not a claim about acquisition cost. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial Real
open scoped BigOperators Classical

variable {V Copy I B : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype Copy] [Fintype I] [Nonempty I] [DecidableEq I] [Fintype B] [LinearOrder B] [Nonempty B]

set_option maxHeartbeats 13000000 in
theorem finite_uncloned_sparse_M6
    (graph : Finset (V×V)) (reg : ∀ v,GraphCutMoments.degree graph v=3)
    (L : UChart (Copy:=Copy) (I:=I) (B:=B) graph)
    (G : MainIncidence.Layout graph (uMark graph) (realCell L.physical) 10)
    (hsize : 7776*(Fintype.card I:ℚ)*(4*10*(Fintype.card I:ℚ))/
      (FiniteGrowth.coefficient G.gamma (1/4))^2<Fintype.card V)
    (t : I→ℚ) (ht : Function.Injective t) (ht0 : ∀ i,t i≠0)
    (A R : ℕ) (ε : ℝ) (hε : 0≤ε) (hQ : 2≤Fintype.card I)
    (hFast : (2:ℝ)≤ε*sqrt (Fintype.card I:ℝ))
    (hBox : ∀ j : ℕ,
        (j:ℝ)*log (2*(Fintype.card I:ℝ))≤ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) →
        ((exactBox (outsideInterval A R) L.physical*(Fintype.card V+1)*(j+1):ℕ):ℝ)≤
          exp (ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)))
    (hRoom : ∀ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4)*Fintype.card V)^2≤
      16*(10:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 →
      3*ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)≤((d/2:ℕ):ℝ)*log 2 ∧
      Fintype.card (JetIndex (fun _i : I=>nominalOrder I (9*Fintype.card V) R) × Fin (Fintype.card V+1))
        < 2^(d-d/2)) :
    HighWitness L.physical (uMark graph) 10 G.gamma G.symbols t
      (fun _=>nominalOrder I (9*Fintype.card V) R) (Fintype.card V+1)
      (fun σ=>trimV (Fintype.card V+1) (actualH L.physical (uMark graph) t
        (printedMix A R) ((uSource L).compile (Fintype.card V+1)) σ)) ε := by
  let ell := Fintype.card V+1
  have hell : 0<ell := Nat.succ_pos _
  have hGrade : ((∑ f : UFactor graph,(uSource L).base f)+4*(ell-1))*R<
      ∑ _i : I,nominalOrder I (9*Fintype.card V) R := by
    dsimp only [ell]
    rw [uncloned_compiled_nominal L reg]
    exact nominal_grid_strict (I:=I) _ _
  have hVars : Fintype.card V≤1*Fintype.card V := by simp
  obtain ⟨out,hOut,hMod⟩ := uncloned_compiled_terminal L ell hell t (printedMix A R)
  have hf : (2:ℝ)*(1:ℕ)≤ε*sqrt (Fintype.card I:ℝ) := by norm_num at ⊢; exact hFast
  exact finite_printed_row_M6 L.physical (uMark graph) graph 10 G hsize t ht ht0 A R
    _ ell ((uSource L).compile ell) (uSource L).base 4 ((uSource L).compile_graded ell)
    hGrade out hOut hMod 1 ε hε hQ hVars hf hBox hRoom

set_option maxHeartbeats 13000000 in
theorem finite_cloned_sparse_M6
    (graph : Finset (V×V)) (reg : ∀ v,GraphCutMoments.degree graph v=3)
    (L : CChart (Copy:=Copy) (I:=I) (B:=B) graph
      (MainClonedCNF.leftSlot graph reg) (MainClonedCNF.rightSlot graph reg))
    (G : MainIncidence.Layout graph (cMark graph) (realCell L.physical) 32)
    (hsize : 7776*(Fintype.card I:ℚ)*(4*32*(Fintype.card I:ℚ))/
      (FiniteGrowth.coefficient G.gamma (1/4))^2<Fintype.card V)
    (t : I→ℚ) (ht : Function.Injective t) (ht0 : ∀ i,t i≠0)
    (A R : ℕ) (ε : ℝ) (hε : 0≤ε) (hQ : 2≤Fintype.card I)
    (hFast : (8:ℝ)≤ε*sqrt (Fintype.card I:ℝ))
    (hBox : ∀ j : ℕ,
        (j:ℝ)*log (2*(Fintype.card I:ℝ))≤ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) →
        ((exactBox (outsideInterval A R) L.physical*(Fintype.card (V×Fin 4)+1)*(j+1):ℕ):ℝ)≤
          exp (ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)))
    (hRoom : ∀ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4)*Fintype.card V)^2≤
      16*(32:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 →
      3*ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)≤((d/2:ℕ):ℝ)*log 2 ∧
      Fintype.card (JetIndex (fun _i : I=>nominalOrder I (29*Fintype.card V) R) × Fin (Fintype.card (V×Fin 4)+1))
        < 2^(d-d/2)) :
    HighWitness L.physical (cMark graph) 32 G.gamma G.symbols t
      (fun _=>nominalOrder I (29*Fintype.card V) R) (Fintype.card (V×Fin 4)+1)
      (fun σ=>trimV (Fintype.card (V×Fin 4)+1) (actualH L.physical (cMark graph) t
        (printedMix A R) ((cSource L).compile (Fintype.card (V×Fin 4)+1)) σ)) ε := by
  let ell := Fintype.card (V×Fin 4)+1
  have hell : 0<ell := Nat.succ_pos _
  have hGrade : ((∑ f : CFactor graph,(cSource L).base f)+4*(ell-1))*R<
      ∑ _i : I,nominalOrder I (29*Fintype.card V) R := by
    dsimp only [ell]
    rw [cloned_compiled_nominal L reg]
    exact nominal_grid_strict (I:=I) _ _
  have hVars : Fintype.card (V×Fin 4)≤4*Fintype.card V := by
    rw [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm]
  obtain ⟨out,hOut,hMod⟩ := cloned_compiled_terminal L ell hell t (printedMix A R)
  have hf : (2:ℝ)*(4:ℕ)≤ε*sqrt (Fintype.card I:ℝ) := by norm_num at ⊢; exact hFast
  exact finite_printed_row_M6 L.physical (cMark graph) graph 32 G hsize t ht ht0 A R
    _ ell ((cSource L).compile ell) (cSource L).base 4 ((cSource L).compile_graded ell)
    hGrade out hOut hMod 4 ε hε hQ hVars hf hBox hRoom

#print axioms finite_uncloned_sparse_M6
#print axioms finite_cloned_sparse_M6
end P5MainBalance.M6.Sparse
