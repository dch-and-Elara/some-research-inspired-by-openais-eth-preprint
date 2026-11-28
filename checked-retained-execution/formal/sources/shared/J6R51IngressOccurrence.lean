import J6R51IngressParser
import Mathlib.Data.List.NodupEquivFin

/-! Replacing the arbitrary old occurrence listing by actual parse
order keeps the literal equality-tree semantics and half incidences.
The tree shape and edge identities stay fixed; its attachment of
successive external ports is selected by the parsed encounter order. -/
namespace J6R51Ingress
noncomputable section
open scoped Classical
open Std.Sat J7R9Compiler J7R9Subdivision J7R9EqualityTree J7R9DirectedTree
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000

theorem occurrence_order_all {V : Type*} (H : CNF V) (o : Occurrence H) :
    o∈occurrenceOrder H :=
  List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨o.1,rfl⟩,List.mem_ofFn.mpr ⟨o.2,rfl⟩⟩

theorem occurrence_order_nodup {V : Type*} (H : CNF V) :
    (occurrenceOrder H).Nodup := by
  let f : ClauseIndex H→List (Occurrence H) :=
    fun i => List.ofFn (fun j : Fin (H.get i).length => ⟨i,j⟩)
  have E : occurrenceOrder H=(List.ofFn (fun i : ClauseIndex H=>i)).flatMap f := by
    simp [occurrenceOrder,occurrenceRows,List.flatMap,List.map_ofFn,Function.comp_def,f]
  rw [E,List.nodup_flatMap]
  constructor
  · intro i _
    apply List.nodup_ofFn_ofInjective
    intro j k eq
    cases eq
    rfl
  · have A : (List.ofFn (fun i : ClauseIndex H=>i)).Nodup :=
      List.nodup_ofFn_ofInjective Function.injective_id
    apply A.imp
    intro i j neq o A B
    obtain ⟨k,ek⟩ := List.mem_ofFn.mp A
    obtain ⟨l,el⟩ := List.mem_ofFn.mp B
    exact neq (congrArg Sigma.fst (ek.trans el.symm))

variable {V : Type*} [DecidableEq V] (H : CNF V)

def forVariable (v : V) : List (Occurrence H) :=
  (occurrenceOrder H).filter (fun o=>decide ((literal H o).1=v))

theorem for_variable_exact (v : V) (o : Occurrence H) :
    o∈forVariable H v ↔ (literal H o).1=v := by
  simp only [forVariable,List.mem_filter,decide_eq_true_eq,occurrence_order_all,true_and]

theorem for_variable_perm (v : V) : (forVariable H v).Perm (occurrences H v) := by
  apply (List.perm_ext_iff_of_nodup ((occurrence_order_nodup H).filter _)
    (Finset.nodup_toList _)).mpr
  intro o
  change o∈forVariable H v ↔ o∈occurrences H v
  rw [for_variable_exact,mem_occurrences]

def orderedExternal (v : V) : List (Wire H) := (forVariable H v).map Sum.inl

def orderedVar (v : V) : List (List (Half H)) :=
  halfGates ((orderedExternal H v).map (fun w => (w,true))) (internal H v)

theorem ordered_shape (v : V) : shape ((orderedExternal H v).map (fun w => (w,true))).length
    (internal H v).length := by
  have X := treeShape H v
  have N : (orderedExternal H v).length=(external H v).length :=
    ((for_variable_perm H v).map Sum.inl).length_eq
  simpa only [List.length_map,N] using X

theorem ordered_degree (v : V) {g : List (Half H)} (hm : g∈orderedVar H v) :
    g.length≤3 := half_degree _ _ (ordered_shape H v) g hm

theorem ordered_var_flat_count (v : V) (z : Half H) :
    J7R10Counts.countByEq (orderedVar H v).flatten z=
      J7R10Counts.countByEq (physicalVar H v).flatten z := by
  let a := (orderedExternal H v).map (fun w => (w,true))
  let b := (external H v).map (fun w => (w,true))
  let e := internal H v
  have mp : a.Perm b := ((for_variable_perm H v).map (Sum.inl : Occurrence H→Wire H)).map
    (fun w => (w,true))
  have x := half_multiplicity a e (ordered_shape H v) z
  have y := half_multiplicity b e (by simpa only [b,e,List.length_map] using treeShape H v) z
  have z0 := mp.countP_eq (fun w=>decide (w=z))
  change J7R10Counts.countByEq (halfGates a e).flatten z=
    J7R10Counts.countByEq (halfGates b e).flatten z
  simp only [J7R10Counts.countByEq,List.count_eq_countP,Bool.beq_eq_decide_eq] at x y ⊢
  rw [x,z0,←y]
theorem ordered_boolean_tree (v : V) (x : Wire H→Bool) :
    (∀ g∈orderedVar H v,agrees (fun h=>x h.1) g) ↔
      ∀ g∈physicalVar H v,agrees (fun h=>x h.1) g := by
  let a := orderedExternal H v
  let b := external H v
  let e := internal H v
  have pa : ((a.map (fun w => (w,true))).map Prod.fst)=a := by simp [List.map_map,Function.comp_def]
  have pb : ((b.map (fun w => (w,true))).map Prod.fst)=b := by simp [List.map_map,Function.comp_def]
  have sa : shape a.length e.length := by
    simpa only [a,e,List.length_map] using ordered_shape H v
  have sb : shape b.length e.length := treeShape H v
  change (∀ g∈halfGates (a.map (fun w => (w,true))) e,agrees (fun h=>x h.1) g) ↔
    ∀ g∈halfGates (b.map (fun w => (w,true))) e,agrees (fun h=>x h.1) g
  rw [same_bit_eval, same_bit_eval,pa,pb,gates_agree _ _ _ sa,gates_agree _ _ _ sb]
  have eM : (a++e).Perm (b++e) := ((for_variable_perm H v).map Sum.inl).append_right e
  unfold agrees
  constructor <;> rintro ⟨j,hj⟩ <;> refine ⟨j,?_⟩ <;> intro w hw
  · exact hj w (eM.mem_iff.mpr hw)
  · exact hj w (eM.mem_iff.mp hw)

#print axioms occurrence_order_all
#print axioms occurrence_order_nodup
#print axioms for_variable_exact
#print axioms for_variable_perm
#print axioms ordered_shape
#print axioms ordered_degree
#print axioms ordered_var_flat_count
#print axioms ordered_boolean_tree
end
end J6R51Ingress
