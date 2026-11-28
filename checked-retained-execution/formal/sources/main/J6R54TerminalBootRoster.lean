import J6R54TerminalBootLineage
import J6R53OldOwnerLive
import J6R51OnlineCore

/-! R53's measured immediate owner re-key is attached to the same
actual online sourceState and to the synchronized mathematical
Gate history of this physical path. No complete all-path raw roster
is an input. Initial paid data and the actual local group and name
words remain separate inputs; their generation is not assumed free. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6ActiveRun J6R26DescriptorTree J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R34ChildPath J6R36ChildFramedRoute J6R49SourceLayout
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R50SourceProducer J6R51Online J6R53OldOwner
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 42000000
set_option maxRecDepth 5600
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate gate : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (M : OnlineMachine T key prec tw bw page rate)
variable (g0 : r.host.Row⊕r.host.Col→Option (CodeGate (Word gate)))

abbrev RosterAt {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c) :=
  CompleteRoster (sourceState M p w).site.oldKey
    (parentData (sourceState M p w) (gateHistory T g0 p))

structure ActualOwnerWords {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (incoming : RosterAt M g0 p w) (u : (Plan sel).Slot (p.ticket w).child) where
  groups : Meter (List (Word 6))
  groupLaw : groups.result=incoming.order.map (fun x=>(ownerGroupRow (sourceState M p w).site x).group)
  inj : Function.Injective (sourceState M p w).site.oldKey
  names : Meter (List (Word (sourceState M (.step p w) u).site.ownerWidth))
  nameLaw : names.result=(bornOwnerOrder (sourceState M p w)
    (useCompleteRoster (sourceState M p w)
      (parentData (sourceState M p w) (gateHistory T g0 p)) incoming groups.result groupLaw).result).map
    (sourceState M (.step p w) u).site.oldKey

def measuredRosterStep {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (incoming : RosterAt M g0 p w) (u : (Plan sel).Slot (p.ticket w).child)
    (words : ActualOwnerWords M g0 p w incoming u) :
    Meter (RosterAt M g0 (.step p w) u) :=
  let site := sourceState M p w
  let advance := (M.demand site u).result.advance
  propagateResidentOwners site (gateHistory T g0 p) incoming words.groups words.groupLaw
    words.inj advance words.names words.nameLaw

structure PathRosterProgram where
  initial : ∀ w : (Plan sel).Slot r, Meter (RosterAt M g0 .root w)
  stepWords : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (incoming : RosterAt M g0 p w) (u : (Plan sel).Slot (p.ticket w).child),
    ActualOwnerWords M g0 p w incoming u

variable (P : PathRosterProgram M g0)

def runRosterAlong :
    {c : Call (PhysicalHost f ell)} → (p : Path sel r c) → (w : (Plan sel).Slot c)→
      Meter (RosterAt M g0 p w)
  | _,.root,w=>P.initial w
  | _,.step p w,u=>
    let old := runRosterAlong p w
    let next := measuredRosterStep M g0 p w old.result u (P.stepWords p w old.result u)
    ⟨next.result,old.steps+next.steps⟩

theorem actual_path_roster_copies_actual_advance
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : (Plan sel).Slot (p.ticket w).child) :
    let old := runRosterAlong M g0 P p w
    let next := measuredRosterStep M g0 p w old.result u (P.stepWords p w old.result u)
    runRosterAlong M g0 P (.step p w) u=⟨next.result,old.steps+next.steps⟩ := rfl

theorem actual_path_roster_covers_every_retained_and_new_owner
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : c.host.Row⊕c.host.Col) :
    ⟨(sourceState M p w).site.oldKey u,parentData (sourceState M p w) (gateHistory T g0 p) u⟩ ∈
      (runRosterAlong M g0 P p w).result.raw := by
  let R := (runRosterAlong M g0 P p w).result
  change _∈R.raw
  rw [R.exactRows]
  exact List.mem_map.mpr ⟨u,R.complete u,rfl⟩

end
#print axioms measuredRosterStep
#print axioms actual_path_roster_copies_actual_advance
#print axioms actual_path_roster_covers_every_retained_and_new_owner
end J6R54TerminalBoot
