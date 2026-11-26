import P5MainBalanceM6DirectAnchor
import P5MainBalanceM6SourceFinite

/-! Direct cloned M.6 with the literal factor recipe and original
nominal degree 12N. The count/parity premises of the generic layer are
discharged. This finite interface retains only the structural layout and
numeric resource margins, not a semantic assumption about the answer. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial Real
open scoped BigOperators Classical

variable {I : Type*} [Fintype I]

noncomputable def nominalOrder (I : Type*) [Fintype I] (d R : ℕ) :=
  d*R/Fintype.card I+1

theorem nominal_grid_strict (d R : ℕ) [Nonempty I] :
    d*R<∑ _i : I,nominalOrder I d R := by
  let Q := Fintype.card I
  let H := d*R
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  unfold nominalOrder
  rw [Nat.mul_add,Nat.mul_one]
  change H<Q*(H/Q)+Q
  calc
    H = H%Q+Q*(H/Q) := (Nat.mod_add_div H Q).symm
    _ = Q*(H/Q)+H%Q := Nat.add_comm _ _
    _ < _ := Nat.add_lt_add_left (Nat.mod_lt _ Fintype.card_pos) _

namespace Direct

variable {V Copy B : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype Copy] [Nonempty I] [DecidableEq I] [Fintype B] [LinearOrder B] [Nonempty B]

set_option maxHeartbeats 14000000 in
theorem finite_direct_cloned_M6
    (graph : Finset (V×V)) (reg : ∀ v,GraphCutMoments.degree graph v=3)
    (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph
      (MainClonedCNF.leftSlot graph reg) (MainClonedCNF.rightSlot graph reg))
    (G : MainIncidence.Layout graph (MainClonedCNF.pinPort graph) (realCell L.physical) 24)
    (hsize : 7776*(Fintype.card I:ℚ)*(4*24*(Fintype.card I:ℚ))/
      (FiniteGrowth.coefficient G.gamma (1/4))^2<Fintype.card V)
    (t : I→ℚ) (ht : Function.Injective t) (ht0 : ∀ i,t i≠0)
    (A R : ℕ) (ε : ℝ) (hε : 0≤ε) (hQ : 2≤Fintype.card I)
    (hFast : (8:ℝ)≤ε*sqrt (Fintype.card I:ℝ))
    (hBox : ∀ j : ℕ,
        (j:ℝ)*log (2*(Fintype.card I:ℝ))≤ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ) →
        ((exactBox (outsideInterval A R) L.physical*1*(j+1):ℕ):ℝ)≤
          exp (ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)))
    (hRoom : ∀ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4)*Fintype.card V)^2≤
      16*(24:ℚ)*(Fintype.card I:ℚ)*(d:ℚ)^2 →
      3*ε*(Fintype.card V:ℝ)/sqrt (Fintype.card I:ℝ)≤((d/2:ℕ):ℝ)*log 2 ∧
      Fintype.card (JetIndex (fun _i : I=>nominalOrder I (12*Fintype.card V) R) × Fin 1)
        < 2^(d-d/2)) :
    HighWitness L.physical (MainClonedCNF.pinPort graph) 24 G.gamma G.symbols t
      (fun _=>nominalOrder I (12*Fintype.card V) R) 1
      (fun σ=>trimV 1 (actualH L.physical (MainClonedCNF.pinPort graph) t
        (printedMix A R) (recipe L) σ)) ε := by
  have hGrade : ((∑ f : Factor graph,width f)+0*(1-1))*R<
      ∑ _i : I,nominalOrder I (12*Fintype.card V) R := by
    rw [sum_width_eq_port_card,MainClonedCNF.port_card graph reg,zero_mul,add_zero]
    exact nominal_grid_strict (I:=I) _ _
  have hVars : Fintype.card (V×Fin 4)≤4*Fintype.card V := by
    rw [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm]
  obtain ⟨out,hOut,hMod⟩ := direct_terminal_witness L t (printedMix A R)
  have hFast' : (2:ℝ)*(4:ℕ)≤ε*sqrt (Fintype.card I:ℝ) := by norm_num at ⊢; exact hFast
  exact finite_printed_row_M6 L.physical (MainClonedCNF.pinPort graph) graph 24 G hsize
    t ht ht0 A R _ 1 (recipe L) width 0 (graded_literal L) hGrade out hOut hMod
    4 ε hε hQ hVars hFast' hBox hRoom

#print axioms finite_direct_cloned_M6
end Direct

#print axioms nominal_grid_strict
end P5MainBalance.M6
