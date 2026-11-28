import J6R49DFSModeTrace

/-! Every element of the authenticated mode transcript is reached by
the actual cursor, and every group in the fixed group loop is reached
by its measured left-product prefix. Proof transcripts do not become
an evaluator-side catalogue. -/
namespace J6R49DFS
open AOracleMachineTime A1R10 A1R12 J6R22Active J6R25PreparedSupply J6R48DFS
open J6R15ModeCost (State Pulse Runs)

set_option autoImplicit false
set_option maxRecDepth 2400
set_option maxHeartbeats 5600000

variable {q n : ℕ} {A : Type*}
local notation "W" => J6R15ModeCost.Word q

theorem append_mode_prefix (op : A→List W→Meter A)
    (start mid last : Pending q n) (a b c : A) (ka kb kc : ℕ)
    (left : ModePrefix op start a ka mid b kb)
    (right : ModePrefix op mid b kb last c kc) :
    ModePrefix op start a ka last c kc := by
  induction right with
  | begin => exact left
  | after _ emit ih => exact .after ih emit

theorem every_transcript_row_is_visited (op : A→List W→Meter A) (X : List (List ℕ)) (wanted : List ℕ)
    (initial : Pending q n) (acc : A) (fee : ℕ)
    (trace : Runs n initial.state X (.ascend [])) (hm : wanted∈X) :
    ∃ (now : Pending q n) (outer : A) (charge : ℕ) (raw : List W) (next : State q),
      ModePrefix op initial acc fee now outer charge ∧ now.pulse.result=.emit raw next ∧
        raw.map J6R15ModeCost.Word.val=wanted := by
  induction X generalizing initial acc fee with
  | nil => simp at hm
  | cons head tail ih =>
    cases e : initial.pulse.result with
    | again next => exact (initial.no_again e).elim
    | halt =>
      have H := (J6R15ModeCost.one_paid_event initial.state initial.valid (head::tail) trace).1
      change J6R15ModeCost.NextExact n (head::tail) initial.pulse.result at H
      rw [e] at H
      cases H
    | emit raw next =>
      obtain ⟨rest,ident,_,later⟩ := initial.next_data e trace
      have hh := (List.cons.inj ident).1
      have he := (List.cons.inj ident).2
      rcases List.mem_cons.mp hm with now|smaller
      · exact ⟨initial,acc,fee,raw,next,.begin,e,hh.symm.trans now.symm⟩
      · rw [←he] at later
        obtain ⟨P,u,K,raw',st,pf,found,word⟩ :=
          ih (initial.tail e) (op acc raw).result (fee+initial.pulse.steps+(op acc raw).steps)
            later smaller
        exact ⟨P,u,K,raw',st,append_mode_prefix op initial (initial.tail e) P acc
          (op acc raw).result u fee (fee+initial.pulse.steps+(op acc raw).steps) K
          (.after .begin e) pf,found,word⟩

theorem every_left_group_is_visited {p ell : ℕ} {fw : List (A1R10.Word p)}
    (hp : 0<p) (read : Fin 64→Meter (UVBlock fw ell))
    (init : UVBlock fw ell) (fee : ℕ) (g : Fin 64) :
    ∃ (left : List (Fin 64)) (inner : UVBlock fw ell) (k : ℕ),
      GroupPrefix hp read init fee (g::left) inner k := by
  have search (more : List (Fin 64)) (acc : UVBlock fw ell) (bill : ℕ)
      (state : GroupPrefix hp read init fee more acc bill) (h : g∈more) :
      ∃ (left : List (Fin 64)) (inner : UVBlock fw ell) (k : ℕ),
        GroupPrefix hp read init fee (g::left) inner k := by
    induction more generalizing acc bill with
    | nil => simp at h
    | cons i is ih =>
      rcases List.mem_cons.mp h with eq|later
      · subst i
        exact ⟨is,acc,bill,state⟩
      · exact ih _ _ (LeftPrefix.after state) later
  have present : g∈groupOrder 64 := by
    rw [groupOrder,List.mem_ofFn]
    exact ⟨g,rfl⟩
  exact search (groupOrder 64) init fee LeftPrefix.begin present

#print axioms append_mode_prefix
#print axioms every_transcript_row_is_visited
#print axioms every_left_group_is_visited
end J6R49DFS
