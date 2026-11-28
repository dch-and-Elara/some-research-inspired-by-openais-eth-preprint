import J6R51IngressRawGraph
import J6R51IngressKeyRank

/-! Number an actual edge directly from raw CNF and its declaration
roster. The graph list is physically minted in this call. Search
charges bit comparisons and a streaming rank counter. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R49RootIngress J6R50RootIngress J6R27OriginalGate J7R9Compiler J7R10Plant
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12500000

def keyWidth {h d j : ℕ} : WireKey h d j→ℕ
  | .original _ _ => h+d
  | .tree x _ => x.length+j

theorem eq_wire_fee {h d j : ℕ} (a b : WireKey h d j) :
    (eqWire a b).steps≤11+5*keyWidth a := by
  cases a with
  | original a k =>
    cases b with
    | original b l =>
      have u := (eq_raw_bits_exact a.val b.val).2
      have v := (eq_raw_bits_exact k.val l.val).2
      rw [a.property] at u
      rw [k.property] at v
      dsimp only [eqWire,keyWidth]
      omega
    | tree => dsimp only [eqWire,keyWidth]; omega
  | tree a k =>
    cases b with
    | original => dsimp only [eqWire,keyWidth]; omega
    | tree b l =>
      have u := (eq_raw_bits_exact a b).2
      have v := (eq_raw_bits_exact k.val l.val).2
      rw [k.property] at v
      dsimp only [eqWire,keyWidth]
      omega

theorem seek_wire_fee {h d j q : ℕ} (k : WireKey h d j) (one start : Word q)
    (rows : List (WireKey h d j)) (W : ℕ) (fit : ∀ z∈rows,keyWidth z≤W) :
    (seekWire k one start rows).steps≤2+rows.length*(17+5*W+12*q) := by
  induction rows generalizing start with
  | nil => simp [seekWire]
  | cons a as ih =>
    have ht : (eqWire a k).steps≤11+5*W :=
      (eq_wire_fee a k).trans (Nat.add_le_add_left (Nat.mul_le_mul_left 5 (fit a List.mem_cons_self)) 11)
    have counter : (addWord start one).steps=12*q := by
      change (addBits start.val one.val).steps=_
      rw [(addBits_exact start.val one.val (start.property.trans one.property.symm)).2.2,start.property]
    have t := ih (addWord start one).result (fun z hz => fit z (List.mem_cons_of_mem _ hz))
    cases h : (eqWire a k).result <;>
      simp only [seekWire,h,Bool.false_eq_true,if_false,if_true,List.length_cons] <;>
      rw [Nat.add_mul,Nat.one_mul] <;> omega

def rankRawCNF {h d j q : ℕ} (v : WireKey h d j) (declares : List (List Bool)) (F : BitsCNF) :
    Meter (Option (Word q)) :=
  let G := compileGraph (h:=h) (d:=d) (j:=j) declares F
  let R := seekWire v (wordOne q) (wordAt q 0) G.result.edges
  ⟨R.result,G.steps+R.steps+6*q+9⟩

theorem actual_generated_graph_rank {V : Type} [DecidableEq V] [Fintype V] {h d j q : ℕ}
    (F : CNF V) (s : DeclaredOrder V) (code : V→List Bool) (inj : Function.Injective code)
    (hh : 0<h) (hd : 0<d) (hj : 0<j) (hq : 0<q)
    (fitH : (guardedInOrder F s.roster).length≤2^h)
    (fitD : ∀ row∈guardedInOrder F s.roster,row.length≤2^d)
    (fitJ : ∀ v,(occurrences (guardedInOrder F s.roster) v).length-3≤2^j)
    (fitQ : (wireOrder (guardedInOrder F s.roster) (guardRoster s)).length≤2^q)
    (v : Wire (guardedInOrder F s.roster)) :
    let H := guardedInOrder F s.roster
    let key := keyOf (h:=h) (d:=d) (j:=j) H (guardCode code) v
    (rankRawCNF (q:=q) key (s.roster.map code) (codeCNF code F)).result=
      some (wordAt q ((wireRank H (guardRoster s)) v).val) := by
  dsimp only [rankRawCNF]
  rw [(raw_graph_exact F s code inj hh hd hj fitH fitD fitJ).1]
  exact raw_wire_rank_from_chosen_list (guardedInOrder F s.roster) (guardRoster s)
    (guardCode code) (guard_code_injective code inj) fitH fitD fitJ hq fitQ v

#print axioms eq_wire_fee
#print axioms seek_wire_fee
#print axioms actual_generated_graph_rank
end J6R51Ingress
