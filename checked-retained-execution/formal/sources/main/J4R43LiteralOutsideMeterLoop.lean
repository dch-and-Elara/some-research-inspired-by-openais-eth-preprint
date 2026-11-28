import J4R43LiteralOutsideMeterBase
import J4R43LiteralOutsideCost

/-! Executes every original bounded-degree source truth table on its
actual ports, then sums and multiplies in the receiving ring. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles J6R9PacketCoeff
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5500000
set_option maxRecDepth 2400
set_option Elab.async false
set_option autoImplicit false

variable {R A : Type} [CommRing R] [Fintype A]

def measuredFinite (combine : R→R→R) (neutral : R) (step : A→NativeMeter R) : NativeMeter R :=
  foldNative combine neutral ((Finset.univ : Finset A).toList.map step)

theorem measuredFinite_bounds (combine : R→R→R) (neutral : R) (step : A→NativeMeter R)
    (d a r : ℕ)
    (stepBound : ∀ x,(step x).addressOps≤d ∧ (step x).tableOps≤a ∧ (step x).ringOps≤r) :
    (measuredFinite combine neutral step).addressOps≤Fintype.card A*d ∧
      (measuredFinite combine neutral step).tableOps≤Fintype.card A*a ∧
      (measuredFinite combine neutral step).ringOps≤Fintype.card A*(r+1) := by
  unfold measuredFinite
  obtain ⟨ha,ht,hr⟩ := foldNative_cost_exact combine neutral
    ((Finset.univ : Finset A).toList.map step)
  simp only [List.map_map,Finset.sum_map_toList,List.length_map,
    Finset.length_toList,Finset.card_univ,Function.comp_apply] at ha ht hr
  rw [ha,ht,hr,Nat.mul_add,Nat.mul_one]
  constructor
  · exact le_trans (Finset.sum_le_sum fun x _=>(stepBound x).1) (by simp)
  constructor
  · exact le_trans (Finset.sum_le_sum fun x _=>(stepBound x).2.1) (by simp)
  · apply Nat.add_le_add_right
    exact le_trans (Finset.sum_le_sum fun x _=>(stepBound x).2.2) (by simp)

theorem measuredFinite_sum (step : A→NativeMeter R) :
    (measuredFinite (·+·) 0 step).value=∑ j : A,(step j).value := by
  rw [measuredFinite,foldNative_sum,List.map_map,Finset.sum_map_toList]
  rfl

theorem measuredFinite_prod (step : A→NativeMeter R) :
    (measuredFinite (·*·) 1 step).value=∏ j : A,(step j).value := by
  rw [measuredFinite,foldNative_prod,List.map_map,Finset.prod_map_toList]
  rfl

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ}
local notation "E" => DWire F
local notation "N" => oldColumnNetwork F reg
variable (t : ℤ) (κ : R) (σ : W→Bool)

def measuredColumnTerm (P : PhysicalPacking N a (Fin 64)) (u : DOld F)
    (x : ColumnArgs F reg u→Bool) : NativeMeter R := by
  let step : ColumnArgs F reg u→NativeMeter R := fun q => paidWeight F reg P t κ (edge q.val) (x q)
  let out : NativeMeter R := measuredFinite (R:=R) (A:=ColumnArgs F reg u) (fun x y : R => x*y) 1 step
  exact ⟨bit R (oldColumnTruth F reg σ (.inr u) x)*out.value,
    out.addressOps,out.tableOps+1,out.ringOps+1⟩

theorem measured_column_term_exact (P : PhysicalPacking N a (Fin 64)) (u : DOld F) (x : ColumnArgs F reg u→Bool) :
    (measuredColumnTerm F reg t κ σ P u x).value=localColumnTerm F reg P t κ σ u x := by
  unfold measuredColumnTerm localColumnTerm
  dsimp only
  rw [measuredFinite_prod]
  congr 1
  exact Finset.prod_congr rfl (fun q _=>paid_weight_exact F reg P t κ (edge q.val) (x q))

theorem measured_column_term_bounds (P : PhysicalPacking N a (Fin 64)) (u : DOld F) (x : ColumnArgs F reg u→Bool) :
    (measuredColumnTerm F reg t κ σ P u x).addressOps≤3*Fintype.card E ∧
      (measuredColumnTerm F reg t κ σ P u x).tableOps≤1 ∧
      (measuredColumnTerm F reg t κ σ P u x).ringOps≤7 := by
  let step := fun q : ColumnArgs F reg u=>paidWeight F reg P t κ (edge q.val) (x q)
  have costs := measuredFinite_bounds (·*·) 1 step (Fintype.card E) 0 1
    (fun e=> by
      obtain ⟨a,b,c⟩ := paid_weight_bounds F reg P t κ (edge e.val) (x e)
      exact ⟨a.le,b.le,c⟩)
  have arity : Fintype.card (ColumnArgs F reg u)≤3 := by
    rw [←Nat.card_eq_fintype_card]
    exact physical_column_arity F reg u
  dsimp only [measuredColumnTerm]
  change (measuredFinite (·*·) 1 step).addressOps≤_ ∧
    (measuredFinite (·*·) 1 step).tableOps+1≤1 ∧
    (measuredFinite (·*·) 1 step).ringOps+1≤7
  exact ⟨costs.1.trans (Nat.mul_le_mul_right _ arity),by omega,by omega⟩

def measuredColumnValue (P : PhysicalPacking N a (Fin 64)) (u : DOld F) : NativeMeter R := by
  let step : (ColumnArgs F reg u→Bool)→NativeMeter R := measuredColumnTerm F reg t κ σ P u
  exact measuredFinite (A:=ColumnArgs F reg u→Bool) (fun x y : R => x+y) 0 step

theorem measured_column_value_exact (P : PhysicalPacking N a (Fin 64)) (u : DOld F) :
    (measuredColumnValue F reg t κ σ P u).value=localColumnValue F reg P t κ σ u := by
  rw [measuredColumnValue,measuredFinite_sum,localColumnValue]
  exact Finset.sum_congr rfl (fun x _=>measured_column_term_exact F reg t κ σ P u x)

theorem measured_column_bounds (P : PhysicalPacking N a (Fin 64)) (u : DOld F) :
    (measuredColumnValue F reg t κ σ P u).addressOps≤24*Fintype.card E ∧
      (measuredColumnValue F reg t κ σ P u).tableOps≤8 ∧
      (measuredColumnValue F reg t κ σ P u).ringOps≤64 := by
  dsimp only [measuredColumnValue]
  have cost := measuredFinite_bounds (·+·) 0 (measuredColumnTerm F reg t κ σ P u)
    (3*Fintype.card E) 1 7 (measured_column_term_bounds F reg t κ σ P u)
  have arity : Fintype.card (ColumnArgs F reg u)≤3 := by
    rw [←Nat.card_eq_fintype_card]
    exact physical_column_arity F reg u
  have input : Fintype.card (ColumnArgs F reg u→Bool)≤8 := by
    rw [Fintype.card_fun,Fintype.card_bool]
    exact Nat.pow_le_pow_right (by decide) arity
  have h : (8:ℕ)*(3*Fintype.card E)=24*Fintype.card E := by ring
  refine ⟨cost.1.trans ((Nat.mul_le_mul_right _ input).trans h.le),?_,?_⟩
  · exact cost.2.1.trans (by simpa using Nat.mul_le_mul_right 1 input)
  · exact cost.2.2.trans (by simpa using Nat.mul_le_mul_right 8 input)

def measuredOutsideValue (P : PhysicalPacking N a (Fin 64)) : NativeMeter R := by
  let step : DOld F→NativeMeter R := measuredColumnValue F reg t κ σ P
  exact measuredFinite (A:=DOld F) (fun x y : R => x*y) 1 step

theorem measured_outside_exact (P : PhysicalPacking N a (Fin 64)) :
    (measuredOutsideValue F reg t κ σ P).value=factorizedValue F reg P t κ σ := by
  rw [measuredOutsideValue,measuredFinite_prod,factorizedValue]
  exact Finset.prod_congr rfl (fun u _=>measured_column_value_exact F reg t κ σ P u)

theorem measured_outside_bounds (P : PhysicalPacking N a (Fin 64)) :
    (measuredOutsideValue F reg t κ σ P).addressOps≤oldRowSize F*(24*Fintype.card E) ∧
      (measuredOutsideValue F reg t κ σ P).tableOps≤oldRowSize F*8 ∧
      (measuredOutsideValue F reg t κ σ P).ringOps≤oldRowSize F*65 := by
  dsimp only [measuredOutsideValue]
  simpa only [oldRowSize,Fintype.card_sum] using (measuredFinite_bounds (·*·) 1 (measuredColumnValue F reg t κ σ P)
    (24*Fintype.card E) 8 64 (measured_column_bounds F reg t κ σ P))

#print axioms measuredFinite_bounds
#print axioms measuredFinite_sum
#print axioms measuredFinite_prod
#print axioms measured_column_term_exact
#print axioms measured_column_term_bounds
#print axioms measured_column_value_exact
#print axioms measured_column_bounds
#print axioms measured_outside_exact
#print axioms measured_outside_bounds
end
end J4R43LiteralOutside

