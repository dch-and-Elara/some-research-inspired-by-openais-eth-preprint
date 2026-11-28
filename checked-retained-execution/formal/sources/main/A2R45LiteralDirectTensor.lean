import A2R45LiteralDirectA3
import A2R45LiteralDirectPath
import J6R10Repack

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

/-! The actual clause/adjacent-equality rows of the direct A2 simulation,
with their distinct Y and pinned Z ports. This is a concrete tensor on
the source's simulated network, prior to physical seat/order/child setup. -/
namespace A2R45Literal
open scoped Classical BigOperators
open Std.Sat J7R9Compiler Acquisition J6R10Repack

noncomputable section
variable {V : Type} [DecidableEq V] (F : CNF V)

abbrev DirectLink := Σ v : V, Fin ((directPath (occurrences F v)).length)
abbrev DirectRow := ClauseIndex F ⊕ DirectLink F

def directArity : DirectRow F→ℕ
  | .inl c => (F.get c).length
  | .inr _ => 2

abbrev DirectPort := Σ r : DirectRow F, Fin (directArity F r)
abbrev DirectWire := Σ r : DirectRow F, Fin (directArity F r)×Bool
abbrev DirectCol := Occurrence F ⊕ DirectPort F

def directEndpoints (e : DirectLink F) : Occurrence F×Occurrence F :=
  (directPath (occurrences F e.1)).get e.2

def directOccurrence : (r : DirectRow F) → Fin (directArity F r) → Occurrence F
  | .inl c,j => ⟨c,j⟩
  | .inr e,j => if j.val=0 then (directEndpoints F e).1 else (directEndpoints F e).2

def directOwner (e : DirectWire F) : DirectCol F :=
  if e.2.2 then .inr ⟨e.1,e.2.1⟩ else .inl (directOccurrence F e.1 e.2.1)

def directNetwork : Network (DirectWire F) (DirectRow F) (DirectCol F) :=
  ⟨Sigma.fst,directOwner F⟩

def directGate : (r : DirectRow F) → (Fin (directArity F r)→Bool) → Bool
  | .inl c,x => decide (∃ j : Fin (F.get c).length,x j=(literal F ⟨c,j⟩).2)
  | .inr _,x => decide (x (0:Fin 2)=x (1:Fin 2))

def directGateTable (r : DirectRow F) (x : (Fin (directArity F r)×Bool)→Bool) : Bool :=
  a3Table (directGate F r) x

theorem actual_direct_column_onto : Function.Surjective (directOwner F) := by
  rintro (⟨c,j⟩|⟨r,j⟩)
  · exact ⟨⟨.inl c,j,false⟩,rfl⟩
  · exact ⟨⟨r,j,true⟩,rfl⟩

theorem actual_direct_row_wire_bound (w : ∀ cl∈F,cl.length≤3) (r : DirectRow F) :
    Fintype.card (Fin (directArity F r)×Bool)≤6 := by
  rw [a3_row_card]
  cases r with
  | inl c => exact Nat.mul_le_mul_left 2 (w _ (List.get_mem F c))
  | inr e => exact (by decide : 2*2≤6)

theorem actual_direct_row_truth_iff (x : Occurrence F→Bool) :
    (∀ r, directGate F r (x ∘ directOccurrence F r)=true) ↔ directAccepts F x := by
  constructor
  · intro h
    refine ⟨fun c=>of_decide_eq_true (h (.inl c)),?_⟩
    intro v e he
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
    have q := of_decide_eq_true (h (.inr ⟨v,i⟩))
    change x (directEndpoints F ⟨v,i⟩).1=x (directEndpoints F ⟨v,i⟩).2 at q
    simpa only [directEndpoints,hi] using q
  · rintro ⟨hc,he⟩ (c|e)
    · exact decide_eq_true (hc c)
    · have hm := List.get_mem (directPath (occurrences F e.1)) e.2
      exact decide_eq_true (he e.1 _ hm)

variable [Fintype V]
variable {K : Type*} [CommRing K]

def directPinOnes (z : DirectPort F→Bool) : K :=
  if z=(fun _=>true) then 1 else 0

def directColumnTensor (x : DirectWire F→Bool) : K :=
  equalityTensor (directOwner F) x * directPinOnes F (fun p=>x ⟨p.1,p.2,true⟩)

def directPinned (x : Occurrence F→Bool) : DirectCol F→Bool :=
  Sum.elim x (fun _=>true)

theorem actual_direct_columns_eliminate (g : (DirectWire F→Bool)→K) :
    (∑ y, directColumnTensor F y*g y)=
      ∑ x : Occurrence F→Bool,g (directPinned F x ∘ directOwner F) := by
  simp only [directColumnTensor,mul_assoc]
  rw [equalityTensor_sum _ (actual_direct_column_onto F)]
  calc
    _ = ∑ p : (Occurrence F→Bool)×(DirectPort F→Bool),
         directPinOnes F p.2*g (Sum.elim p.1 p.2 ∘ directOwner F) := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow _ _ _)
      intro u
      congr 1
      apply congrArg g
      funext i
      cases h : directOwner F i <;>
        simp only [Function.comp_apply,h,Sum.elim_inl,Sum.elim_inr,
          Equiv.sumArrowEquivProdArrow_apply_fst,Equiv.sumArrowEquivProdArrow_apply_snd]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      simp only [directPinOnes,ite_mul,one_mul,zero_mul,Fintype.sum_ite_eq']
      rfl

theorem actual_direct_gates_contract (x : Occurrence F→Bool) :
    extension (rowProduct (fun r z=>bit (K:=K) (directGateTable F r z)))
      (fun e=>-bit (directPinned F x (directOwner F e))) =
    ∏ r,bit (K:=K) (directGate F r (x ∘ directOccurrence F r)) := by
  rw [extension_rowProduct]
  apply Finset.prod_congr rfl
  intro r _
  have args :
      (fun j : Fin (directArity F r)×Bool =>
        -bit (directPinned F x (directOwner F ⟨r,j⟩))) =
      (fun j => if j.2 then (-1:K) else -bit (x (directOccurrence F r j.1))) := by
    funext j
    rcases j with ⟨j,b⟩
    cases b <;> rfl
  rw [args]
  let summation (d : DecidableEq (Fin (directArity F r))) : K := by
    letI := d
    exact ∑ z : (Fin (directArity F r)×Bool)→Bool,
      bit (a3Table (directGate F r) z) *
        ∏ i : Fin (directArity F r)×Bool,
          lag (z i) (if i.2 then (-1:K) else -bit (x (directOccurrence F r i.1)))
  change summation (instDecidableEqFin _) = _
  calc
    _ = summation (Classical.decEq _) := congrArg summation (Subsingleton.elim _ _)
    _ = _ := a3_actual_two_ports_per_coordinate (K:=K) (directGate F r) (x ∘ directOccurrence F r)

theorem actual_direct_counting_tensor (occurs : AllOccur F) :
    (∑ y : DirectWire F→Bool,directColumnTensor F y *
      extension (rowProduct (fun r z=>bit (K:=K) (directGateTable F r z)))
        (fun e=>-bit (y e)))=(PinnedCNF.modelCount F:K) := by
  rw [actual_direct_columns_eliminate]
  have one (x : Occurrence F→Bool) :
      (∏ r,bit (K:=K) (directGate F r (x ∘ directOccurrence F r))) =
        if directAccepts F x then 1 else 0 := by
    by_cases h : directAccepts F x
    · rw [if_pos h]
      exact Finset.prod_eq_one (fun r _=>by
        rw [(actual_direct_row_truth_iff F x).mpr h r]; rfl)
    · rw [if_neg h]
      obtain ⟨r,hr⟩ := not_forall.mp (fun e=>h ((actual_direct_row_truth_iff F x).mp e))
      exact Finset.prod_eq_zero (Finset.mem_univ r) (by
        rw [Bool.eq_false_iff.mpr hr]; rfl)
  simp_rw [Function.comp_apply, actual_direct_gates_contract, one]
  rw [←Finset.sum_filter]
  have eq := direct_path_has_one_extension F occurs
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at eq
  simpa using congrArg (fun n : ℕ=>(n:K)) eq

#print axioms actual_direct_column_onto
#print axioms actual_direct_row_wire_bound
#print axioms actual_direct_row_truth_iff
#print axioms actual_direct_columns_eliminate
#print axioms actual_direct_gates_contract
#print axioms actual_direct_counting_tensor
end
end A2R45Literal
