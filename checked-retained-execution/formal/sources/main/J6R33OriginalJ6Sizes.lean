import J6R28GeneratedRootFrameLiteral
import J6R25StableCensusCompact
import J6R27PrescribedProbeCapacity

/-! Numeric source cardinalities for the J6 reduction: size is measured
in the literal clause list *and* in the declared finite variable list.
The explicit exponential-looking counters are over the printed
polynomial enlargement. The active-root exclusion leaves a fixed
bounded-size source family. -/
namespace J6R33OriginalJ6
open scoped Polynomial
open Std.Sat J6Mesh J7R9Clause J7R10Readout J6R28GeneratedRootFrame
open J6R25StableCensus J6R14LayoutCost J6R27PrescribedProbe J1PPrinted
set_option maxHeartbeats 3200000
set_option maxRecDepth 1500
set_option exponentiation.threshold 524320

theorem clean_clause_count {V : Type} [DecidableEq V] (F : CNF V) :
    (clean F).length≤F.length := by
  induction F with
  | nil => exact le_rfl
  | cons c cs ih =>
    rw [clean]
    split <;> simp only [List.length_cons] <;> omega

theorem literal_wire_size {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (F : CNF V) (three : ∀ c∈F,c.length≤3) :
    Fintype.card V≤mCNF F ∧ mCNF F≤16*(F.length+Fintype.card V) := by
  have n := literal_native_fits F three
  have v : Fintype.card V≤literalNativeSize F := by
    unfold literalNativeSize
    rw [Fintype.card_option]
    omega
  have c : (J7R9SourceInput.H F).length≤F.length+Fintype.card V := by
    unfold J7R9SourceInput.H J6Guard.guardedFormula
    simp only [List.length_append,List.length_map,Finset.length_toList,Finset.card_univ]
    exact Nat.add_le_add_right (clean_clause_count F) _
  refine ⟨v.trans n,?_⟩
  exact (J7R9SourceInput.source_count_size F three).2.2.2.trans (Nat.mul_le_mul_left 16 c)

def activeFloor : ℕ := (2*epsDen)^30*(2:ℕ)^10

theorem small_inputs_have_bounded_universe {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (F : CNF V) (three : ∀ c∈F,c.length≤3)
    (bad : Nat.clog 2 (physicalSize (mCNF F) (literalNativeSize F)) < activeFloor) :
    Fintype.card V+2<2^activeFloor := by
  let m := mCNF F
  let s := physicalSize m (literalNativeSize F)
  have g : Nat.clog 2 s=lambda m := (physicalSize_ceiling _ _ (literal_native_fits F three)).2.2
  have b : b m≤Nat.clog 2 s := by
    rw [g,lambda]
    omega
  exact lt_of_le_of_lt
    (Nat.add_le_add_right (literal_wire_size F three).1 2 |>.trans (dyadic_rounding m).1)
    (Nat.pow_lt_pow_right (by decide) (b.trans_lt bad))

theorem finite_exception_assignments {V : Type} [DecidableEq V] [Fintype V]
    (bound : ℕ) (small : Fintype.card V+2<bound) :
    Fintype.card (V→Bool) ≤ (2:ℕ)^bound := by
  rw [Fintype.card_fun,Fintype.card_bool]
  exact Nat.pow_le_pow_right (by decide)
    (lt_of_le_of_lt (Nat.le_add_right (Fintype.card V) 2) small).le

theorem cell_pair_loop_is_source_polynomial (m : ℕ) :
    (2:ℕ)^(6*a m)*(2:ℕ)^(6*a m)=D m ∧
      (2:ℕ)^(6*a m)≤M m ∧ D m≤M m ∧ K m≤M m ∧ L m≤M m := by
  have P : (2:ℕ)^(6*a m)*(2:ℕ)^(6*a m)=D m := by
    rw [←pow_add]
    unfold a D
    congr 1
    omega
  have hD : D m≤M m := by
    rw [←mesh_product]
    exact Nat.le_mul_of_pos_right _ (by unfold K L; positivity)
  have hK : K m≤M m := by
    rw [←mesh_product]
    exact (Nat.le_mul_of_pos_right _ (by unfold L; positivity)).trans
      (Nat.le_mul_of_pos_left _ (by unfold D; positivity))
  have hP : (2:ℕ)^(6*a m)≤(2:ℕ)^(6*a m)*(2:ℕ)^(6*a m) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  exact ⟨P,(P ▸ hP).trans hD,hD,hK,mesh_length_le_edges m⟩

theorem stable_padding_bit_budget_polynomial (m width l : ℕ) :
    stablePadBudget (a m) (K m) l width ≤
      16*(6*a m+1)*M m + M m*((8*(6*a m)+22)*M m+4)+4+5+
      M m*allPairsPadFee (a m) (K m) l width+7 := by
  obtain ⟨P,h,hD,_,_⟩ := cell_pair_loop_is_source_polynomial m
  unfold stablePadBudget allPairsCap
  rw [P]
  gcongr

#print axioms clean_clause_count
#print axioms literal_wire_size
#print axioms small_inputs_have_bounded_universe
#print axioms finite_exception_assignments
#print axioms cell_pair_loop_is_source_polynomial
#print axioms stable_padding_bit_budget_polynomial
end J6R33OriginalJ6
