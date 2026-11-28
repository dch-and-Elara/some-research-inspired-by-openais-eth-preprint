import J6R26DescriptorTreeOrder
import J6R25PreparedSupplyRelative

/-! Breadth-first descriptor creation before the prepared arithmetic.
Parents precede children, and within a parent the original literal
centre/probe/mode/group order is retained. The order is chosen for
registration, not a claim about the original evaluator's stack.
Multiplicity comes from invocation occurrences, never a set of calls. -/
namespace J6R26DescriptorTree
open scoped Polynomial BigOperators Classical
open Polynomial J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J1PPrinted J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf)

structure Ticket (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (root : Call (PhysicalHost f ell)) where
  parent : Call (PhysicalHost f ell)
  path : NativeReach (Plan sel) root parent
  slot : (Plan sel).Slot parent

noncomputable def Ticket.child (B : Ticket sel r) : Call (PhysicalHost f ell) :=
  (Plan sel).child B.parent B.slot

noncomputable def oneLayer (c : Call (PhysicalHost f ell)) : List (Ticket sel r) :=
  if h : NativeReach (Plan sel) r c then
    (ordered T c).map (fun w=>⟨c,h,w⟩)
  else []

theorem one_layer_children {c : Call (PhysicalHost f ell)} (hc : NativeReach (Plan sel) r c) :
    (oneLayer T c).map Ticket.child=orderedChildren T c := by
  rw [oneLayer,dif_pos hc,List.map_map]
  rfl

noncomputable def literalLayers : ℕ→List (Call (PhysicalHost f ell))
  | 0 => [r]
  | n+1 => (literalLayers n).flatMap (orderedChildren T)

theorem literal_layers_perm (n : ℕ) :
    (literalLayers T n).Perm (occurrences (Plan sel) r n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [literalLayers,occurrences]
    refine (List.Perm.flatMap_left _ (fun c hc=>?_)).trans (ih.flatMap_right (childList (Plan sel)))
    have hm : c∈occurrences (Plan sel) r n := ih.mem_iff.mp hc
    exact ordered_children_same T
      (occurrence_reach_depth (Plan sel) (fun x=>x.depth) (fun _ _=>rfl) r n c hm).1

theorem literal_layers_reach (n : ℕ) {c : Call (PhysicalHost f ell)}
    (hc : c∈literalLayers T n) : NativeReach (Plan sel) r c :=
  (occurrence_reach_depth (Plan sel) (fun x=>x.depth) (fun _ _=>rfl) r n c
    ((literal_layers_perm T n).mem_iff.mp hc)).1

noncomputable def ticketsAt (n : ℕ) : List (Ticket sel r) :=
  (literalLayers T n).flatMap (oneLayer T)

theorem ticket_targets (n : ℕ) :
    (ticketsAt T n).map Ticket.child=literalLayers T (n+1) := by
  rw [ticketsAt,List.map_flatMap,literalLayers]
  have go (xs : List (Call (PhysicalHost f ell)))
      (hx : ∀ c∈xs,NativeReach (Plan sel) r c) :
      xs.flatMap (fun c=>(oneLayer T c).map Ticket.child)=xs.flatMap (orderedChildren T) := by
    induction xs with
    | nil => rfl
    | cons z zs ih =>
      simp only [List.flatMap_cons,one_layer_children T (hx z List.mem_cons_self),
        ih (fun c hc=>hx c (List.mem_cons_of_mem _ hc))]
  exact go _ (fun _=>literal_layers_reach T n)

noncomputable def allTickets : List (Ticket sel r) :=
  (List.range (pathLimit s C)).flatMap (ticketsAt T)

theorem sum_range_shift (a : ℕ→ℕ) (n : ℕ) :
    (∑ j∈Finset.range (n+1),a j)=a 0+∑ j∈Finset.range n,a (j+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]; omega

theorem each_ticket_charged (n : ℕ) :
    (ticketsAt T n).length=(occurrences (Plan sel) r (n+1)).length := by
  rw [←(literal_layers_perm T (n+1)).length_eq,←ticket_targets T n,List.length_map]

theorem all_tickets_count :
    (allTickets T).length+1=
      ∑ j∈Finset.range (pathLimit s C+1),(occurrences (Plan sel) r j).length := by
  rw [allTickets,List.length_flatMap,←List.sum_toFinset _ List.nodup_range,List.toFinset_range,
    sum_range_shift]
  simp only [occurrences,List.length_singleton,Nat.add_comm _ 1]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact each_ticket_charged T j

theorem schedule_ends :
    literalLayers T (pathLimit s C+1)=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro c h
  have v := (literal_layers_perm T _).mem_iff.mp h
  rw [no_relative_terminal_children T] at v
  cases v

#print axioms literal_layers_perm
#print axioms ticket_targets
#print axioms all_tickets_count
#print axioms schedule_ends
end J6R26DescriptorTree


