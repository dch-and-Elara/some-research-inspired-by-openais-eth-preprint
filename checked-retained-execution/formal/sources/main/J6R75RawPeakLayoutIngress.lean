import J6R75RawPeakLayoutWords

/-! Selected live input and label files from the actual Ingress and
R12 greedy producer, including isolated owner commands. The provider's
internal producer working storage is not inferred from its output. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionPacking
open J6R12CollisionSource J6R12CollisionMenu J6R14LayoutCost
open J6R68ActiveInputs J6R10Repack J6R11Collision J6R11CollisionReindex P11FullPacking
open V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10200000
set_option maxRecDepth 3950
set_option Elab.async false

def rawLayoutTargetBits : Target→ℕ
  | .row addr=>1+addr.length
  | .col addr=>1+addr.length

def rawIncidenceLayoutBits (x : List Bool×List Bool) : ℕ := x.1.length+x.2.length

theorem raw_layout_bits_le_of_field_cap {A : Type*} (view : A→ℕ) (cap : ℕ)
    (xs : List A) (fit : ∀ x∈xs,view x≤cap) :
    rawLayoutBits view xs≤cap*xs.length := by
  induction xs with
  | nil=>simp [rawLayoutBits]
  | cons x xs ih=>
    change view x+rawLayoutBits view xs≤cap*(xs.length+1)
    rw [Nat.mul_succ,Nat.add_comm (cap*xs.length)]
    exact Nat.add_le_add (fit x List.mem_cons_self) (ih (fun y hm=>fit y (List.mem_cons_of_mem _ hm)))

section IngressView
variable {E R C : Type*} [Fintype E] {a : ℕ} {N : Network E R C}
variable (I : Full64Input N a) (W : Ingress I)

theorem actual_ingress_commands_and_wire_bytes_have_their_source_capacity :
    let F := I.format
    rawLayoutBits rawLayoutTargetBits W.paid.result.1≤(1+max F.kR F.kC)*I.order.length ∧
    rawLayoutBits rawIncidenceLayoutBits W.paid.result.2=(F.kR+F.kC)*Fintype.card E ∧
    rawLayoutBits rawEdgeLayoutBits (initGraph F.kR F.kC W.paid.result.2).result=
      (F.kR+F.kC+2)*Fintype.card E := by
  let F := I.format
  have cap (u : R⊕C) : rawLayoutTargetBits (F.target u)≤1+max F.kR F.kC := by
    cases u with
    | inl r=>
      change 1+(encodeBits F.kR (F.rCode r)).length≤1+max F.kR F.kC
      rw [encodeBits_length]
      exact Nat.add_le_add_left (Nat.le_max_left _ _) _
    | inr c=>
      change 1+(encodeBits F.kC (F.cCode c)).length≤1+max F.kR F.kC
      rw [encodeBits_length]
      exact Nat.add_le_add_left (Nat.le_max_right _ _) _
  have raw (x : List Bool×List Bool) (hx : x∈I.raw) :
      rawIncidenceLayoutBits x=F.kR+F.kC := by
    unfold Full64Input.raw at hx
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx
    simp only [rawIncidenceLayoutBits,encodeBits_length]
    rfl
  have unlabeled (x : EdgeTape) (mem : x∈F.graph (fun _=>none)) :
      rawEdgeLayoutBits x=F.kR+F.kC+2 := by
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp mem
    simp only [rawEdgeLayoutBits,rawEndLayoutBits,packEdge,packEnd,Option.map_none,Option.getD_none,
      encodeBits_length,Nat.add_zero]
    omega
  dsimp only
  rw [W.commands,W.incidences,(show (initGraph I.format.kR I.format.kC I.raw).result=I.format.graph (fun _=>none) from (initGraph_exact I.format).1)]
  refine ⟨?_,?_,?_⟩
  · rw [←List.length_map (f:=I.format.target)]
    exact raw_layout_bits_le_of_field_cap _ _ _ (fun target ht=>by
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp ht
      exact cap v)
  · rw [raw_layout_bits_fixed _ _ _ raw]
    simp only [Full64Input.raw,List.length_map,Format.graphEdges,F]
  · rw [raw_layout_bits_fixed _ _ _ unlabeled]
    simp only [Format.graph,List.length_map,Format.graphEdges,F]

variable [Fintype R] [Fintype C]

theorem actual_ingress_greedy_keeps_the_complete_original_label_file
    (q : ℕ) :
    let F := I.format
    let inlet := initGraph F.kR F.kC W.paid.result.2
    let chosen := drive F.e F.kR F.kC F.b W.paid.result.1 inlet.result
    let all := runWithIngress I q W
    let final := packFixed F.kR F.kC F.b q a chosen.result.1
    chosen.result=I.run.result ∧
    all.result.vertexLabels=chosen.result.2 ∧ all.result.boxes=final.result.boxes ∧
    all.result.copies=final.result.copies ∧
    gridMemoryBits chosen.result.2=F.b*I.order.length := by
  let F := I.format
  let inlet := initGraph F.kR F.kC W.paid.result.2
  let chosen := drive F.e F.kR F.kC F.b W.paid.result.1 inlet.result
  have correct : chosen.result=I.run.result := by
    unfold chosen inlet Full64Input.run
    rw [W.commands,W.incidences]
  have alphabet : Fintype.card (Fin a→Fin 64)=2^F.b := by
    rw [show F.b=6*a from I.labelWidth,source_alphabet (G:=Fin 64) (by simp) a]
  have rb (v : R) : (fibre F.row v).card≤Fintype.card E := Finset.card_le_univ _
  have cb (v : C) : (fibre F.col v).card≤Fintype.card E := Finset.card_le_univ _
  obtain ⟨z,_,labels,_,_⟩ := drive_exact F alphabet I.order I.distinct I.complete
    (Fintype.card E) rb cb
  have applyLabels : chosen.result.2=I.order.map (fun v=>F.label (z v)) := by
    unfold chosen inlet
    rw [W.commands,W.incidences,(show (initGraph I.format.kR I.format.kC I.raw).result=I.format.graph (fun _=>none) from (initGraph_exact I.format).1)]
    exact labels
  refine ⟨correct,rfl,rfl,rfl,?_⟩
  change gridMemoryBits chosen.result.2=_
  rw [applyLabels]
  have w (b : List Bool) (mem : b∈I.order.map (fun v=>F.label (z v))) : b.length=F.b := by
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp mem
    exact encodeBits_length _ _
  rw [uniform_grid_bits _ _ w,List.length_map]
end IngressView

#print axioms actual_ingress_commands_and_wire_bytes_have_their_source_capacity
#print axioms actual_ingress_greedy_keeps_the_complete_original_label_file
end J6R75RawPeak
