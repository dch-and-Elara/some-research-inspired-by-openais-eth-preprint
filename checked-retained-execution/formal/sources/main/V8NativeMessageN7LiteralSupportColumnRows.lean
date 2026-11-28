import V8NativeMessageN7LiteralSupportColumnWitness
import V8NativeMessageN7LiteralSupportFlat

/-! Literal row elimination in the orientation with old vertices on the
column side. The sum remains over all actual column assignments and
each physical subdivision contributes its own two-port equality. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R9PacketTiles P11FullPacking
open Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 11000000
set_option maxRecDepth 2300
noncomputable section

def equalityPair {R : Type} [CommRing R] (x y : R) : R := (1-x)*(1-y)+x*y

private def flipBits : (Bool→Bool) ≃ Bool×Bool where
  toFun f := (f false,f true)
  invFun p := fun b=>if b then p.2 else p.1
  left_inv f := by funext b; cases b <;> rfl
  right_inv p := rfl

theorem two_port_equality_sum {R : Type} [CommRing R] (x y : R) :
    (∑ u : Bool→Bool, if u false=u true then
      LiteralPortCompiler.affine (u false) x * LiteralPortCompiler.affine (u true) y else 0)=
        equalityPair x y := by
  let f (u : Bool→Bool) := if u false=u true then
    LiteralPortCompiler.affine (u false) x * LiteralPortCompiler.affine (u true) y else 0
  change (∑ u,f u)=_
  rw [Fintype.sum_equiv flipBits f (fun p=>f (flipBits.symm p)) (fun a=>(congrArg f (flipBits.symm_apply_apply a)).symm),
    Fintype.sum_prod_type]
  simp [f,flipBits,LiteralPortCompiler.affine,equalityPair,add_comm]

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
local notation "E" => (DWire F)
local notation "D" => (MainClonedCNF.Port F)
variable {a : ℕ} {R : Type} [CommRing R]
variable (P : PhysicalPacking (oldColumnNetwork F reg) a (Fin 64))

def actualColumnArgument (t : ℤ) (κ : R) (y : E→Bool) (r : E) : R :=
  κ*wholeShiftBit P R t (Sum.elim (fun _=>false) y) r

private theorem columnArgument_reads_no_row_bits (t : ℤ) (κ : R) (x y : E→Bool) (r : E) :
    κ*wholeShiftBit P R t (Sum.elim x y) r=actualColumnArgument F reg P t κ y r := rfl

def literalSubdivisionWeight (t : ℤ) (κ : R) (y : E→Bool) (q : D) : R :=
  equalityPair (actualColumnArgument F reg P t κ y (q,false))
    (actualColumnArgument F reg P t κ y (q,true))

private def weightedEquality (A : E→R) (q : D) (u : Bool→Bool) : R :=
  if u false=u true then LiteralPortCompiler.affine (u false) (A (q,false)) *
    LiteralPortCompiler.affine (u true) (A (q,true)) else 0

private def curryRows : (E→Bool) ≃ (D→Bool→Bool) where
  toFun x q b := x (q,b)
  invFun y e := y e.1 e.2
  left_inv _ := rfl
  right_inv _ := rfl

private theorem true_column_flags_as_indicator (σ : W→Bool) (y : E→Bool) :
    (∏ u : DOld F,bit R (oldRowTruth F reg σ (.inl u) (fun p=>y (edge p.val)))) =
      if originalColumnKeep F reg σ y then 1 else 0 := by
  by_cases h : ∀ u : DOld F,oldRowTruth F reg σ (.inl u) (fun p=>y (edge p.val))=true
  · have k : originalColumnKeep F reg σ y=true := decide_eq_true h
    rw [if_pos k]
    exact Finset.prod_eq_one (fun u _=>by rw [h u]; rfl)
  · have k : originalColumnKeep F reg σ y=false := decide_eq_false h
    rw [if_neg (by rw [k]; decide)]
    obtain ⟨u,hu⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    cases b : oldRowTruth F reg σ (.inl u) (fun p=>y (edge p.val))
    · rfl
    · exact (hu b).elim

theorem original_old_column_term (t : ℤ) (κ : R) (σ : W→Bool) (x y : E→Bool) :
    flatTerm P t κ (oldColumnTruth F reg σ) (Sum.elim x y)=
      if originalColumnKeep F reg σ y then
        ∏ q : D,weightedEquality F (actualColumnArgument F reg P t κ y) q (fun b=>x (q,b))
      else 0 := by
  let A := actualColumnArgument F reg P t κ y
  let f (r : E) := LiteralPortCompiler.affine (x r) (A r)
  let row (q : D) := (if x (q,false)=x (q,true) then 1 else 0 : R)
  let keep := originalColumnKeep F reg σ y
  have flag :
      (∏ v,bit R (oldColumnTruth F reg σ v (fun p=> Sum.elim x y p.val))) =
      (∏ q : D,row q) * (if keep then 1 else 0) := by
    rw [Fintype.prod_sum_type]
    apply congrArg₂ (·*·)
    · refine Finset.prod_congr rfl fun q _=>?_
      rw [subdivision_row_literal]
      simp [row,bit]
    · simp only [actual_column_flags_read_only_its_old_port]
      exact true_column_flags_as_indicator (R:=R) F reg σ y
  have ringRows :
      (∏ r : E,LiteralPortCompiler.affine (Sum.elim x y (.inl r))
        (κ*wholeShiftBit P R t (Sum.elim x y) r)) =
      ∏ q : D,f (q,false)*f (q,true) := by
    simp only [columnArgument_reads_no_row_bits F reg P t κ x y]
    change (∏ r : E,f r)=_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun q _=>?_                 
    rw [Fintype.prod_bool, mul_comm]
  unfold flatTerm
  rw [flag,ringRows]
  change ((∏ q : D,row q)*(if keep then 1 else 0))*
    (∏ q : D,f (q,false)*f (q,true)) = if keep then _ else 0
  by_cases yes : keep=true
  · simp only [if_pos yes,mul_one]
    rw [←Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _=>?_
    by_cases equal : x (q,false)=x (q,true)
    · simp [row,f,weightedEquality,equal,A]
    · simp [row,weightedEquality,equal]
  · simp [yes]

theorem actual_old_column_rows_summed (t : ℤ) (κ : R) (σ : W→Bool) :
    flatSigned P t κ (oldColumnTruth F reg σ)=
      ∑ y : E→Bool,if originalColumnKeep F reg σ y then
        ∏ q : D,literalSubdivisionWeight F reg P t κ y q else 0 := by
  classical
  rw [literal_cubes_sum_columns_first]
  refine Finset.sum_congr rfl fun y _=>?_
  simp only [original_old_column_term]
  by_cases good : originalColumnKeep F reg σ y=true
  · simp only [if_pos good]
    let A := actualColumnArgument F reg P t κ y
    let W (q : D) (u : Bool→Bool) := weightedEquality F A q u
    change (∑ x : E→Bool,∏ q : D,W q (fun b=>x (q,b)))=_
    calc
      _ = ∏ q : D,∑ u : Bool→Bool,W q u := by
        letI : DecidableEq D := Classical.decEq D
        letI : ∀ q : D,Fintype (Bool→Bool) := fun _=>inferInstance
        letI : Fintype (D→Bool→Bool) := Pi.instFintype
        rw [Fintype.prod_sum (κ:=fun _ : D => Bool→Bool) W]
        have exchange := Fintype.sum_equiv (curryRows F)
          (fun x : E→Bool=>∏ q : D,W q (fun b=>x (q,b)))
          (fun x : D→Bool→Bool=>∏ q : D,W q (x q)) (fun _=>rfl)
        refine Eq.trans ?_ exchange
        exact Finset.sum_congr (Finset.ext fun x=>by simp only [Finset.mem_univ]) (fun _ _=>rfl)
      _ = _ := by
        refine Finset.prod_congr rfl fun q _=>?_
        exact two_port_equality_sum (A (q,false)) (A (q,true))
  · simp [good]

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.two_port_equality_sum
#print axioms V8NativeMessage.N7LiteralSupport.original_old_column_term
#print axioms V8NativeMessage.N7LiteralSupport.actual_old_column_rows_summed
