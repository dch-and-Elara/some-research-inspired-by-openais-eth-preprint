
import J7R9Compiler
import J7R9Clause

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000
set_option maxRecDepth 2350
set_option linter.unusedSectionVars false

/-! v9 A2, lines 2337--2348: real source CNF cleanup and projection to
used declared variables, with the exact contribution of the omitted
variables. This is count-preservation, not a preprocessing bit trace. -/
namespace A2R45Literal
open scoped Classical BigOperators
open Std.Sat J7R9Compiler
noncomputable section

variable {V : Type} (F : CNF V)

def seen (v : V) : Prop := ∃ o : Occurrence F,(literal F o).1=v
abbrev Used := {v : V//seen F v}
abbrev Unused := {v : V//¬seen F v}

def keptLiteral (o : Occurrence F) : Used F×Bool :=
  (⟨(literal F o).1,⟨o,rfl⟩⟩,(literal F o).2)

def keptClause (i : ClauseIndex F) : CNF.Clause (Used F) :=
  List.ofFn (fun j : Fin (F.get i).length=>keptLiteral F ⟨i,j⟩)

def keepUsed : CNF (Used F) := List.ofFn (keptClause F)

def usedBits (x : V→Bool) : Used F→Bool := x ∘ Subtype.val

theorem kept_sat (x : V→Bool) : CNF.Sat (usedBits F x) (keepUsed F) ↔ CNF.Sat x F := by
  constructor
  · intro h
    apply (sat_at_positions F x).mpr
    intro i
    unfold CNF.Sat CNF.eval at h
    have hcl := (List.all_eq_true.mp h) (keptClause F i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
    obtain ⟨l,hl,he⟩ := (J7R9Clause.eval_true _ _).mp hcl
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hl
    exact ⟨j,he⟩
  · intro h
    unfold CNF.Sat CNF.eval
    apply List.all_eq_true.mpr
    intro cl hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    obtain ⟨j,he⟩ := (sat_at_positions F x).mp h i
    exact (J7R9Clause.eval_true _ _).mpr ⟨keptLiteral F ⟨i,j⟩,List.mem_ofFn.mpr ⟨j,rfl⟩,he⟩

def SplitUsed : (V→Bool) ≃ ((Used F→Bool)×(Unused F→Bool)) where
  toFun x := (usedBits F x, x ∘ Subtype.val)
  invFun y v := if h : seen F v then y.1 ⟨v,h⟩ else y.2 ⟨v,h⟩
  left_inv x := by funext v; by_cases h : seen F v <;> simp [h,usedBits]
  right_inv y := by
    apply Prod.ext
    · funext v
      exact dif_pos v.property
    · funext v
      exact dif_neg v.property

def keptModelEquiv :
    {x : V→Bool//CNF.Sat x F} ≃
      ({x : Used F→Bool//CNF.Sat x (keepUsed F)} × (Unused F→Bool)) where
  toFun x := (⟨usedBits F x.val,(kept_sat F x.val).mpr x.property⟩,x.val ∘ Subtype.val)
  invFun y := ⟨(SplitUsed F).symm (y.1.val,y.2),by
    apply (kept_sat F _).mp
    have h := congrArg Prod.fst ((SplitUsed F).apply_symm_apply (y.1.val,y.2))
    change usedBits F ((SplitUsed F).symm (y.1.val,y.2))=y.1.val at h
    rw [h]; exact y.1.property⟩
  left_inv x := Subtype.ext ((SplitUsed F).symm_apply_apply x.val)
  right_inv y := by
    have h := (SplitUsed F).apply_symm_apply (y.1.val,y.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · have hp : ((SplitUsed F) ((SplitUsed F).symm (y.1.val,y.2))).2=y.2 :=
        congrArg Prod.snd h
      exact hp

theorem kept_width (w : ∀ cl∈F,cl.length≤3) : ∀ cl∈keepUsed F,cl.length≤3 := by
  intro cl hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  rw [keptClause,List.length_ofFn]
  exact w (F.get i) (List.get_mem F i)

theorem kept_nonempty (w : ∀ cl∈F,0<cl.length) : ∀ cl∈keepUsed F,0<cl.length := by
  intro cl hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  rw [keptClause,List.length_ofFn]
  exact w (F.get i) (List.get_mem F i)

theorem all_kept_declared_variables_occur : AllOccur (keepUsed F) := by
  intro v
  obtain ⟨⟨i,j⟩,h⟩ := v.property
  have he : (keptLiteral F ⟨i,j⟩).1=v := Subtype.ext h
  have hl : keptLiteral F ⟨i,j⟩∈keptClause F i := List.mem_ofFn.mpr ⟨j,rfl⟩
  have hc : keptClause F i∈keepUsed F := List.mem_ofFn.mpr ⟨i,rfl⟩
  apply (variable_position_iff (keepUsed F) v).mp
  apply CNF.mem_of hc
  rw [←he]
  exact CNF.Clause.mem_of hl

variable [Fintype V]

theorem keepUsed_count :
    PinnedCNF.modelCount F =
      PinnedCNF.modelCount (keepUsed F)*2^Nat.card (Unused F) := by
  rw [modelCount_card F,Nat.card_congr (keptModelEquiv F),Nat.card_prod,
    ←modelCount_card (keepUsed F),Nat.card_fun,Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool]

def normalizeSparse [DecidableEq V] : CNF (Used (J7R9Clause.clean F)) :=
  keepUsed (J7R9Clause.clean F)

theorem normalizeSparse_count [DecidableEq V] :
    PinnedCNF.modelCount F=
      PinnedCNF.modelCount (normalizeSparse F)*2^Nat.card (Unused (J7R9Clause.clean F)) :=
  (J7R9Clause.clean_count F).symm.trans (keepUsed_count _)

theorem cleaned_nonempty [DecidableEq V] (h : ∀ cl∈F,0<cl.length) :
    ∀ cl∈J7R9Clause.clean F,0<cl.length := by
  intro cl hc
  obtain ⟨g,hg,_,rfl⟩ := J7R9Clause.clean_mem hc
  let j : Fin g.length := ⟨0,h g hg⟩
  exact List.length_pos_of_mem (List.mem_dedup.mpr (List.get_mem g j))

theorem raw_empty_clause_zero (h : ([] : CNF.Clause V)∈F) :
    PinnedCNF.modelCount F=0 := by
  rw [modelCount_card F,Nat.card_eq_fintype_card,Fintype.card_eq_zero_iff]
  refine ⟨fun x=>?_⟩
  have p := x.property
  unfold CNF.Sat CNF.eval at p
  have e := (List.all_eq_true.mp p) [] h
  cases e

theorem raw_empty_list_power :
    PinnedCNF.modelCount ([] : CNF V)=2^Fintype.card V := by
  rw [modelCount_card]
  let e : {x : V→Bool//CNF.Sat x ([] : CNF V)} ≃ (V→Bool) :=
    ⟨Subtype.val,fun x=>⟨x,rfl⟩,fun _=>rfl,fun _=>rfl⟩
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_bool]

#print axioms kept_sat
#print axioms keptModelEquiv
#print axioms kept_width
#print axioms kept_nonempty
#print axioms all_kept_declared_variables_occur
#print axioms normalizeSparse_count
#print axioms raw_empty_clause_zero
#print axioms raw_empty_list_power
end
end A2R45Literal
