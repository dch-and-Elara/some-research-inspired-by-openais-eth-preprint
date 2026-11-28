import J6R53OldOwnerHeaders
import J6R53OldOwnerNext

/-! Joint live-source owner transition: actual ordered group words
enter the existing R49 selector, actual returned source rows and
same-birth Page keys are paid, and actual next-chart names enter the
rekey. Attach the produced complete byte roster to this Advance. -/
namespace J6R53OldOwner
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R49SourceLayout
open J6ActiveRun J6R50SourceProducer J6R52CacheSource
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3300
set_option maxHeartbeats 14500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page gate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "P" => (v.parent.host.Row⊕v.parent.host.Col)
local notation "V" => (v.child.host.Row⊕v.child.host.Col)
local notation "G" => (Option (CodeGate (Word gate)))

def propagateResidentOwners
    (X : StoredSite T v key prec tw bw page) (gates : P→G)
    (source : CompleteRoster X.site.oldKey (parentData X gates))
    (groups : Meter (List (Word 6)))
    (groupWords : groups.result=source.order.map (fun x=>(ownerGroupRow X.site x).group))
    (inj : Function.Injective X.site.oldKey)
    {u : (@Plan f ell s sel).Slot v.child} (advance : Advance X u)
    (names : Meter (List (Word advance.next.site.ownerWidth)))
    (aligned : names.result=(bornOwnerOrder X
      (useCompleteRoster X (parentData X gates) source groups.result groupWords).result).map
      advance.next.site.oldKey) :
    Meter (CompleteRoster advance.next.site.oldKey
      (parentData advance.next (childGate (T:=T) gates))) :=
  let H := useCompleteRoster X (parentData X gates) source groups.result groupWords
  let next := retainedRosterForNext X gates source H.result inj advance names.result aligned
  ⟨next.result,groups.steps+H.steps+names.steps+next.steps⟩

theorem actual_live_roster_includes_every_owner
    (X : StoredSite T v key prec tw bw page) (gates : P→G)
    (source : CompleteRoster X.site.oldKey (parentData X gates))
    (groups : Meter (List (Word 6)))
    (groupWords : groups.result=source.order.map (fun x=>(ownerGroupRow X.site x).group))
    (inj : Function.Injective X.site.oldKey)
    {u : (@Plan f ell s sel).Slot v.child} (advance : Advance X u)
    (names : Meter (List (Word advance.next.site.ownerWidth)))
    (aligned : names.result=(bornOwnerOrder X
      (useCompleteRoster X (parentData X gates) source groups.result groupWords).result).map
      advance.next.site.oldKey) :
    let paid := propagateResidentOwners X gates source groups groupWords inj advance names aligned
    let H := useCompleteRoster X (parentData X gates) source groups.result groupWords
    let met := bornOwnerData X gates source H.result
    (∀ vertex : V,
      ⟨advance.next.site.oldKey vertex,parentData advance.next (childGate (T:=T) gates) vertex⟩∈
        paid.result.raw) ∧
    paid.steps=groups.steps+(3+(3*X.site.ownerWidth+25)*source.order.length)+names.steps+
      (met.steps+(3+(3*advance.next.site.ownerWidth+6)*names.result.length)+5) := by
  let paid := propagateResidentOwners X gates source groups groupWords inj advance names aligned
  let H := useCompleteRoster X (parentData X gates) source groups.result groupWords
  let next := retainedRosterForNext X gates source H.result inj advance names.result aligned
  refine ⟨?_,?_⟩
  · intro vertex
    change ⟨advance.next.site.oldKey vertex,parentData advance.next (childGate (T:=T) gates) vertex⟩∈paid.result.raw
    rw [paid.result.exactRows]
    exact List.mem_map.mpr ⟨vertex,paid.result.complete vertex,rfl⟩
  · have groupFee : H.steps=3+(3*X.site.ownerWidth+25)*source.order.length :=
      congrArg Meter.steps (actual_group_header_tape X (parentData X gates) source groups.result groupWords)
    have cost := next_roster_charges_only_actual_writes X gates source H.result inj advance names.result aligned
    change groups.steps+H.steps+names.steps+next.steps=_
    rw [groupFee,show next.steps=_ from cost]

#print axioms propagateResidentOwners
#print axioms actual_live_roster_includes_every_owner
end
end J6R53OldOwner
