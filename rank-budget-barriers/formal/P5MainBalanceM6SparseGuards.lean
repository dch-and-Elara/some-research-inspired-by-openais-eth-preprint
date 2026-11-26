import P5MainBalanceM6SparseFamilies
import P5MainBalanceM6PrintedSchedule

/-! Nominal degree and size certificates, separately for the actual
uncloned and cloned optional test lists. Neutral singleton factors are
counted as placed incidences, not as unit-degree evenness tests. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def sparseNominal (n mTest : ℕ) : ℕ :=
  2*(mTest+2*((n+1)-1))

set_option maxHeartbeats 5600000 in
theorem uncloned_nominal_guards (G : Finset (V×V)) (reg : ∀ v,GraphCutMoments.degree G v=3) :
    let n := Fintype.card V
    let mTest := Fintype.card (V⊕G)
    let M := Fintype.card (UPort G)
    2*mTest=5*n ∧ M=5*n ∧ sparseNominal n mTest=9*n ∧ 2*M=10*n := by
  dsimp only
  have h := GraphCutMoments.regular_edge_count G 3 reg
  simp only [sparseNominal,UPort,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,
    Fintype.card_coe]
  omega

set_option maxHeartbeats 5600000 in
theorem cloned_nominal_guards (G : Finset (V×V)) (reg : ∀ v,GraphCutMoments.degree G v=3) :
    let N := Fintype.card V
    let n := Fintype.card (V×Fin 4)
    let mTest := Fintype.card (Direct.Factor G)
    let M := Fintype.card (CPort G)
    n=4*N ∧ 2*mTest=13*N ∧ M=16*N ∧ sparseNominal n mTest=29*N ∧
      sparseNominal n mTest≤9*n ∧ 2*M=32*N := by
  dsimp only
  have h := GraphCutMoments.regular_edge_count G 3 reg
  have hPorts := MainClonedCNF.port_card G reg
  simp only [sparseNominal,CPort,Direct.Factor,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_coe,hPorts]
  omega

theorem sparse_source_ell_positive (n : ℕ) : 0<n+1 := by omega

set_option maxHeartbeats 5600000 in
theorem printed_uncloned_order_exact (G : Finset (V×V)) (reg : ∀ v,GraphCutMoments.degree G v=3) :
    printedOrder (Fintype.card V) (sparseNominal (Fintype.card V) (Fintype.card (V⊕G))) =
      9*Fintype.card V*mainWidth 1 (Fintype.card V)/mainNodes (Fintype.card V)+1 := by
  rw [(uncloned_nominal_guards G reg).2.2.1]
  rfl

set_option maxHeartbeats 5600000 in
theorem printed_cloned_order_exact (G : Finset (V×V)) (reg : ∀ v,GraphCutMoments.degree G v=3) :
    let n := Fintype.card (V×Fin 4)
    printedOrder n (sparseNominal n (Fintype.card (Direct.Factor G))) =
      29*Fintype.card V*mainWidth 1 n/mainNodes n+1 := by
  dsimp only
  rw [(cloned_nominal_guards G reg).2.2.2.1]
  rfl

#print axioms uncloned_nominal_guards
#print axioms cloned_nominal_guards
#print axioms printed_uncloned_order_exact
#print axioms printed_cloned_order_exact
end P5MainBalance.M6.Sparse
