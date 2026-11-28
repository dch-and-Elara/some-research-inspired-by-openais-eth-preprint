import J6R51IngressParser
import J6R49RootIngressFees

/-! For fresh charts the user-supplied declaration list is the
order, not a demand that it match the archived Finset order.
Safety clauses change order only, so exact CNF counting is invariant. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat AOracleMachineTime J6R49RootIngress J7R9Compiler
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10600000

def guardSafety {V : Type*} (v : V) : CNF.Clause (Option V) :=
  [(none,true),(some v,false)]

def guardOldClause {V : Type*} (row : CNF.Clause V) : CNF.Clause (Option V) :=
  (none,false)::row.map J6Guard.mapLit

noncomputable def guardedInOrder {V : Type*} [DecidableEq V] (F : CNF V) (declares : List V) :
    CNF (Option V) := (J7R9Clause.clean F).map guardOldClause++declares.map guardSafety

theorem paid_guard_in_order {V : Type*} [DecidableEq V]
    (F : CNF V) (declares : List V) (code : V→List Bool) (inj : Function.Injective code) :
    (guardedMeter (declares.map code) (codeCNF code F)).result =
      codeCNF (guardCode code) (guardedInOrder F declares) := by
  dsimp only [guardedMeter]
  rw [add_guards_exact,safety_rows_exact,clean_meter_exact,same_clean_code code inj]
  simp [guardedInOrder,codeCNF,guardOldClause,guardSafety,List.map_map,List.map_append,
    Function.comp_def,J6Guard.mapLit,tagLit,guardCode,codeLit]

theorem ordered_guard_perm {V : Type*} [DecidableEq V] [Fintype V]
    (F : CNF V) (declares : List V) (nd : declares.Nodup) (complete : ∀ v,v∈declares) :
    (guardedInOrder F declares).Perm (guarded F) := by
  have same : declares.Perm ((Finset.univ : Finset V).toList) := by
    apply (List.perm_ext_iff_of_nodup nd (Finset.nodup_toList _)).mpr
    intro v
    simp [complete v]
  change ((J7R9Clause.clean F).map guardOldClause++declares.map guardSafety).Perm _
  unfold guarded J7R9SourceInput.H J6Guard.guardedFormula
  exact (same.map guardSafety).append_left _

theorem ordered_guard_count {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V]
    (F : CNF V) (declares : List V) (nd : declares.Nodup) (complete : ∀ v,v∈declares) :
    PinnedCNF.modelCount (guardedInOrder F declares)=1+PinnedCNF.modelCount F := by
  have p := ordered_guard_perm F declares nd complete
  have t (x : Option V→Bool) : CNF.Sat x (guardedInOrder F declares)↔CNF.Sat x (guarded F) := by
    unfold CNF.Sat CNF.eval
    simp only [List.all_eq_true,p.mem_iff]
  have e : {x : Option V→Bool // CNF.Sat x (guardedInOrder F declares)} ≃
      {x : Option V→Bool // CNF.Sat x (guarded F)} := (Equiv.refl _).subtypeEquiv t
  rw [modelCount_card, Nat.card_congr e,←modelCount_card]
  exact J7R9Clause.guarded_clean_count F

theorem parse_fresh_order_raw {V : Type*} [DecidableEq V] {h d : ℕ}
    (F : CNF V) (declares : List V) (code : V→List Bool) (inj : Function.Injective code)
    (hh : 0<h) (hd : 0<d) (fitH : (guardedInOrder F declares).length≤2^h)
    (fitD : ∀ row∈guardedInOrder F declares,row.length≤2^d) :
    (parseInput (h:=h) (d:=d) (declares.map code) (codeCNF code F)).result =
      (occurrenceOrder (guardedInOrder F declares)).map
        (guardToken (guardedInOrder F declares) (guardCode code)) := by
  dsimp only [parseInput]
  rw [paid_guard_in_order F declares code inj]
  exact parse_guard_exact _ _ hh hd fitH fitD

#print axioms paid_guard_in_order
#print axioms ordered_guard_perm
#print axioms ordered_guard_count
#print axioms parse_fresh_order_raw
end J6R51Ingress
