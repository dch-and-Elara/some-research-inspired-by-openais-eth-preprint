import J6R52FreshShapeCore
import J6R51IngressPhysicalFile

/-! Changing only the submitted order of the guards preserves every
occurrence multiplicity and hence both actual graph dimensions. This
matches original printed dimensions without asserting archival row or
seat equality. The physical size using the literal source measure is
therefore exactly preserved, not merely of the same order. -/
namespace J6R52FreshShape
open scoped Classical BigOperators
open Std.Sat J7R9Compiler J7R9Subdivision J7R9Size J7R10Plant
open J6R51Ingress J6R49RootIngress J6R28GeneratedRootFrame J6Mesh
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 13500000
set_option maxRecDepth 2700

def variablesByRow {A : Type*} (H : CNF A) : List A :=
  H.flatMap (fun row=>row.map Prod.fst)

theorem occurrence_tape_variables {A : Type*} (H : CNF A) :
    (occurrenceOrder H).map (fun o => (literal H o).1)=variablesByRow H := by
  let f := fun o : Occurrence H => (literal H o).1
  let g := fun row : CNF.Clause A => row.map Prod.fst
  have perRow (i : ClauseIndex H) :
      (List.ofFn (fun j : Fin (H.get i).length => (⟨i,j⟩ : Occurrence H))).map f=g (H.get i) := by
    rw [List.map_ofFn]
    change List.ofFn (Prod.fst ∘ (H.get i).get)=g (H.get i)
    rw [←List.map_ofFn,List.ofFn_get]
  change ((occurrenceRows H).flatten.map f)=(H.map g).flatten
  rw [List.map_flatten]
  change ((List.ofFn (fun i : ClauseIndex H=>List.ofFn (fun j : Fin (H.get i).length=>⟨i,j⟩))).map
    (List.map f)).flatten = _
  rw [List.map_ofFn]
  have same :
      (List.map f ∘ fun i : ClauseIndex H=>List.ofFn (fun j : Fin (H.get i).length=>⟨i,j⟩)) =
        g ∘ H.get := funext perRow
  rw [same,←List.map_ofFn,List.ofFn_get]

theorem variable_occurrences_count {A : Type*} [DecidableEq A] (H : CNF A) (v : A) :
    (occurrences H v).length=List.countP (fun x=>decide (x=v)) (variablesByRow H) := by
  rw [←occurrence_tape_variables,List.countP_map]
  rw [(for_variable_perm H v).length_eq.symm,List.countP_eq_length_filter]
  rfl

theorem occurrence_card_from_tape {A : Type*} (H : CNF A) :
    Fintype.card (Occurrence H)=(variablesByRow H).length := by
  classical
  have N := full_roster_length (occurrenceOrder H) (occurrence_order_nodup H)
    (occurrence_order_all H)
  rw [←occurrence_tape_variables,List.length_map]
  exact N.symm

theorem perm_preserves_half_wire_dimensions {A : Type*} [DecidableEq A] [Fintype A]
    {G H : CNF A} (p : G.Perm H) :
    nSubdiv G=nSubdiv H ∧ nWires G=nWires H := by
  have e : (variablesByRow G).Perm (variablesByRow H) := p.flatMap (fun _ _=>List.Perm.refl _)
  have same (v : A) : (occurrences G v).length=(occurrences H v).length := by
    rw [variable_occurrences_count,variable_occurrences_count]
    exact e.countP_eq (fun v' => decide (v'=v))
  have count : nSubdiv G=nSubdiv H := by
    unfold nSubdiv
    rw [wire_card,wire_card,occurrence_card_from_tape,occurrence_card_from_tape,e.length_eq]
    simp only [same]
  exact ⟨count,by rw [twice_subdiv,twice_subdiv,count]⟩

variable {A : Type} [DecidableEq A] [Fintype A]

theorem fresh_printed_source_dimensions (F : CNF A) (order : DeclaredOrder A) :
    let H := guardedInOrder F order.roster
    nSubdiv H=J7R10Readout.qCNF F ∧ nWires H=J7R10Readout.mCNF F ∧
      sourceNative H=literalNativeSize F := by
  let p := ordered_guard_perm F order.roster order.distinct order.complete
  obtain ⟨q,m⟩ := perm_preserves_half_wire_dimensions p
  exact ⟨q,m,congrArg (fun n=>Fintype.card (Option A)+n) p.length_eq⟩

theorem fresh_literal_physical_size_exact (F : CNF A) (order : DeclaredOrder A) :
    let H := guardedInOrder F order.roster
    physicalSize (nWires H) (sourceNative H)=
      physicalSize (J7R10Readout.mCNF F) (literalNativeSize F) := by
  dsimp only
  rw [(fresh_printed_source_dimensions F order).2.1,(fresh_printed_source_dimensions F order).2.2]

theorem fresh_printed_field_width_exact [Nonempty A]
    (F : CNF A) (order : DeclaredOrder A) (three : ∀ row∈F,row.length≤3) :
    let H := guardedInOrder F order.roster
    printedFieldWidth (nWires H) (nSubdiv H)=
      printedFieldWidth (J7R10Readout.mCNF F) (literalNativeSize F) := by
  dsimp only [printedFieldWidth]
  rw [chosen_source_schedule_same F order three,fresh_literal_physical_size_exact F order]

#print axioms occurrence_tape_variables
#print axioms variable_occurrences_count
#print axioms occurrence_card_from_tape
#print axioms perm_preserves_half_wire_dimensions
#print axioms fresh_printed_source_dimensions
#print axioms fresh_literal_physical_size_exact
#print axioms fresh_printed_field_width_exact
end J6R52FreshShape
