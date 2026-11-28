import J6R64BootSeatsProvider

/-! Direct specialization of the R55 assembler to the bounded source
tables. The actual physical occurrence, truth tags and addon writer
are unchanged. The call's original occurrence and owner preparation
meters remain explicit. -/
namespace J6R64.BootSeats
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6ActiveRun J6ActiveSchedule J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R26DescriptorTree J6R31RootResidentTables J6R32ChildResidentTransfer
open J6R34RootAtlas J6R36ChildFramedRoute J6R48GeneratedAddons J6R48RawRoute
open J6R49SourceLayout J6R50SourceProducer J6R55TerminalOrigin J6R58BootScope J6R53OldOwner
open J6R10Repack P11FullPacking J6R9PacketScopes J6OrientedHost J6R20Ancestor
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4900
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page own gw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (input : Meter (OccurrenceInput T v key prec tw bw page))
variable {name : v.parent.host.Row⊕v.parent.host.Col→Word own}
variable {value : v.parent.host.Row⊕v.parent.host.Col→OwnerData gw key prec page}
variable {tags : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (source : Meter (CompleteRoster name value))
variable (tagLaw : ∀ x,(value x).origin=tags x) (inj : Function.Injective name)
local notation "I" => (input.result)

def boundedAssembly
    (pairOrder : (I).native.result.physical.order=pairedPorts (I).geometry.edges)
    (ownerTape : Meter (OwnerTape I name))
    (fallback : Addon own (dim v) key prec page) :
    Meter (StoredSite T v key prec tw bw page) :=
  assembleOriginSite tagLaw inj input source (bootProvider I name pairOrder ownerTape fallback)

theorem bounded_assembly_is_the_actual_r55_program
    (pairOrder : (I).native.result.physical.order=pairedPorts (I).geometry.edges)
    (ownerTape : Meter (OwnerTape I name))
    (fallback : Addon own (dim v) key prec page) :
    let D := bootProvider I name pairOrder ownerTape fallback
    let out := boundedAssembly input source tagLaw inj pairOrder ownerTape fallback
    out.result.input=I ∧ out.result.origins=tags ∧
    out.result.site.install.result=some ((compileOccurrence I).native.physical.order.map
      (fun h=>⟨((compileOccurrence I).native.physical.record h).address,
        addonAt T v name tags (occurrencePageWord I) h⟩)) ∧
    out.steps=input.steps+source.steps+(ownerTape.steps+(canonicalSeatBank I).steps+3)+
      (projectOriginTape source.result.raw).steps+
      (emit (readBootAddon D source.result) (compileOccurrence I).native.physical.order).steps := by
  have h := same_occurrence_and_paid_tag_sidecar tagLaw inj input source
    (bootProvider I name pairOrder ownerTape fallback)
  exact ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩

#print axioms boundedAssembly
#print axioms bounded_assembly_is_the_actual_r55_program
end
end J6R64.BootSeats
