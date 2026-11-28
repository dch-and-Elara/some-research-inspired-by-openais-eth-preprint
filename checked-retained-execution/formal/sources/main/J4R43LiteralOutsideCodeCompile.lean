import J4R43LiteralOutsideScalarCode
import J4R43LiteralOutsideMeterLoop

/-! Native bounded-degree compilation to p-bit scalar code. Input
Boolean flags are the actual old-column tables on their own physical
ports, and signs are not used when compiling matching geometry. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
open A1R10 A1R12 AOracleMachineTime
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5800000
set_option maxRecDepth 2200
set_option Elab.async false

def codeSum : List ScalarCode→ScalarCode := List.foldr ScalarCode.add (.flag false)
def codeProd : List ScalarCode→ScalarCode := List.foldr ScalarCode.mul (.flag true)

variable {R : Type} [CommRing R]

theorem code_sum_meaning (x : R) (s : List ScalarCode) :
    (codeSum s).denote x=(s.map (ScalarCode.denote x)).sum := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    change k.denote x+(codeSum s).denote x=k.denote x+(s.map (ScalarCode.denote x)).sum
    rw [ih]

theorem code_prod_meaning (x : R) (s : List ScalarCode) :
    (codeProd s).denote x=(s.map (ScalarCode.denote x)).prod := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    change k.denote x*(codeProd s).denote x=k.denote x*(s.map (ScalarCode.denote x)).prod
    rw [ih]

theorem code_prod_size (s : List ScalarCode) (max : ℕ) (small : ∀ k∈s,k.size≤max) :
    (codeProd s).size≤1+s.length*(max+1) := by
  induction s with
  | nil => simp [codeProd,ScalarCode.size]
  | cons k s ih =>
    have kSize := small k List.mem_cons_self
    have tail := ih (fun v m=>small v (List.mem_cons_of_mem _ m))
    change k.size+(codeProd s).size+1≤1+(s.length+1)*(max+1)
    rw [Nat.succ_mul s.length]
    omega

theorem code_sum_size (s : List ScalarCode) (max : ℕ) (small : ∀ k∈s,k.size≤max) :
    (codeSum s).size≤1+s.length*(max+1) := by
  induction s with
  | nil => simp [codeSum,ScalarCode.size]
  | cons k s ih =>
    have kSize := small k List.mem_cons_self
    have tail := ih (fun v m=>small v (List.mem_cons_of_mem _ m))
    change k.size+(codeSum s).size+1≤1+(s.length+1)*(max+1)
    rw [Nat.succ_mul s.length]
    omega

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ}
local notation "E" => DWire F
local notation "N" => oldColumnNetwork F reg

def chooseFactor (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (e : E) (b : Bool) : ScalarCode :=
  if (measuredColumnHit F reg P t e).1 && b then .sub (.flag true) .unit else .flag true

theorem actual_factor_code (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (v : E) (b : Bool) (κ : R) :
    (chooseFactor F reg P t v b).denote κ=columnArgumentWeight F reg P t κ v b := by
  rw [←paid_weight_exact F reg P t κ v b]
  unfold chooseFactor paidWeight
  dsimp only
  split <;> rfl

theorem actual_factor_code_size (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (v : E) (b : Bool) :
    (chooseFactor F reg P t v b).size≤3 := by
  unfold chooseFactor
  split <;> decide

variable (t : ℤ) (σ : W→Bool)

def localCode (P : PhysicalPacking N a (Fin 64)) (u : DOld F) (b : ColumnArgs F reg u→Bool) :
    ScalarCode := by
  let weights : List ScalarCode := (Finset.univ : Finset (ColumnArgs F reg u)).toList.map 
    (fun e=>chooseFactor F reg P t (edge e.val) (b e))
  exact .mul (.flag (oldColumnTruth F reg σ (.inr u) b)) (codeProd weights)

theorem local_code_exact (P : PhysicalPacking N a (Fin 64)) (u : DOld F) (b : ColumnArgs F reg u→Bool) (κ : R) :
    (localCode F reg t σ P u b).denote κ=localColumnTerm F reg P t κ σ u b := by
  unfold localCode localColumnTerm
  dsimp only [ScalarCode.denote]
  rw [code_prod_meaning,List.map_map,Finset.prod_map_toList]
  congr 1
  exact Finset.prod_congr rfl (fun e _=>actual_factor_code F reg P t (edge e.val) (b e) κ)

theorem local_code_size (P : PhysicalPacking N a (Fin 64)) (u : DOld F) (b : ColumnArgs F reg u→Bool) :
    (localCode F reg t σ P u b).size≤15 := by
  let step := fun e : ColumnArgs F reg u=>chooseFactor F reg P t (edge e.val) (b e)
  let tape := (Finset.univ : Finset (ColumnArgs F reg u)).toList.map step
  have r := code_prod_size tape 3 (fun k h=>by
    obtain ⟨e,_,he⟩ := List.mem_map.mp h
    rw [←he]
    exact actual_factor_code_size F reg P t (edge e.val) (b e))
  have width : tape.length≤3 := by
    simp only [tape,List.length_map,Finset.length_toList,Finset.card_univ,←Nat.card_eq_fintype_card]
    exact physical_column_arity F reg u
  change 1+(codeProd tape).size+1≤15
  omega

def columnCode (P : PhysicalPacking N a (Fin 64)) (u : DOld F) : ScalarCode := by
  let f := localCode F reg t σ P u
  exact codeSum (((Finset.univ : Finset (ColumnArgs F reg u→Bool)).toList.map f))

theorem original_column_code_value (P : PhysicalPacking N a (Fin 64)) (u : DOld F) (κ : R) :
    (columnCode F reg t σ P u).denote κ=localColumnValue F reg P t κ σ u := by
  unfold columnCode localColumnValue
  dsimp only
  rw [code_sum_meaning,List.map_map,Finset.sum_map_toList]
  exact Finset.sum_congr rfl (fun b _=>local_code_exact F reg t σ P u b κ)

theorem original_column_code_size (P : PhysicalPacking N a (Fin 64)) (u : DOld F) :
    (columnCode F reg t σ P u).size≤129 := by
  let step := localCode F reg t σ P u
  let tape := (Finset.univ : Finset (ColumnArgs F reg u→Bool)).toList.map step
  have r := code_sum_size tape 15 (fun k h=>by
    obtain ⟨e,_,he⟩ := List.mem_map.mp h
    rw [←he]
    exact local_code_size F reg t σ P u e)
  have degree : Fintype.card (ColumnArgs F reg u)≤3 := by
    rw [←Nat.card_eq_fintype_card]
    exact physical_column_arity F reg u
  have words : tape.length≤8 := by
    simp only [tape,List.length_map,Finset.length_toList,Finset.card_univ,Fintype.card_fun,Fintype.card_bool]
    exact Nat.pow_le_pow_right (by decide) degree
  change (codeSum tape).size≤129
  omega

def originalOutsideCode (P : PhysicalPacking N a (Fin 64)) : ScalarCode :=
  codeProd ((Finset.univ : Finset (DOld F)).toList.map (columnCode F reg t σ P))

theorem original_outside_code_value (P : PhysicalPacking N a (Fin 64)) (κ : R) :
    (originalOutsideCode F reg t σ P).denote κ=factorizedValue F reg P t κ σ := by
  unfold originalOutsideCode factorizedValue
  rw [code_prod_meaning,List.map_map,Finset.prod_map_toList]
  exact Finset.prod_congr rfl (fun u _=>original_column_code_value F reg t σ P u κ)

theorem original_outside_code_size (P : PhysicalPacking N a (Fin 64)) :
    (originalOutsideCode F reg t σ P).size≤1+oldRowSize F*130 := by
  unfold originalOutsideCode
  have r := code_prod_size ((Finset.univ : Finset (DOld F)).toList.map (columnCode F reg t σ P)) 129
    (fun k h=>by
      obtain ⟨v,_,he⟩ := List.mem_map.mp h
      rw [←he]
      exact original_column_code_size F reg t σ P v)
  simpa only [List.length_map,Finset.length_toList,Finset.card_univ,Fintype.card_sum,oldRowSize]
    using r

#print axioms code_sum_meaning
#print axioms code_prod_meaning
#print axioms code_sum_size
#print axioms code_prod_size
#print axioms actual_factor_code
#print axioms actual_factor_code_size
#print axioms local_code_exact
#print axioms local_code_size
#print axioms original_column_code_value
#print axioms original_column_code_size
#print axioms original_outside_code_value
#print axioms original_outside_code_size
end
end J4R43LiteralOutside

