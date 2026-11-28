import J6R55TerminalOriginTape
import J6R50SourceProducerOnline
import J6R48GeneratedAddonsNative

/-! Form the initial StoredSite from the measured occurrence and the
actual mounted origin table. Only raw geometry/seat queries are
additional inputs: neither an origin table nor an origin equality
for a supplied StoredSite occurs here. -/
namespace J6R55TerminalOrigin
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R20Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R41StructuredAllPaths J6R27OriginalGate J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R50SourceProducer J6R34RootAtlas J6R49SourceLayout J6R53OldOwner
open J6R48GeneratedAddons
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 4400
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page own gate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

structure BootPortWords (I : OccurrenceInput T v key prec tw bw page) (name : (v.parent.host.Row⊕v.parent.host.Col)→Word own) where
  seatWidth : ℕ
  seats : Meter (List (RefRow seatWidth (SeatField (dim v) page)))
  queries : (Port v.parent.host.Edge)→Meter (Word own × Word seatWidth × Bool)
  ownerQuery : ∀ h,(queries h).result.1=name (owner v.parent.host.network h)
  sideExact : ∀ h,(queries h).result.2.2=side h
  seatHit : ∀ h,(⟨(queries h).result.2.1,rawSeat (occurrencePageWord I) h⟩ : RefRow seatWidth _)∈seats.result
  seatUnique : ∀ (h : (Port v.parent.host.Edge)) (x : RefRow seatWidth (SeatField (dim v) page)),
    x∈seats.result→x.address=(queries h).result.2.1→x.payload=rawSeat (occurrencePageWord I) h
  fallback : Addon own (dim v) key prec page

variable {I : OccurrenceInput T v key prec tw bw page} {name : (v.parent.host.Row⊕v.parent.host.Col)→Word own}
variable {value : (v.parent.host.Row⊕v.parent.host.Col)→OwnerData gate key prec page} {tags : (v.parent.host.Row⊕v.parent.host.Col)→Origin key prec page}
variable (D : BootPortWords I name)
variable (R : CompleteRoster name value) (tagLaw : ∀ x,(value x).origin=tags x)
variable (inj : Function.Injective name)

include tagLaw inj in
theorem compiled_input_reads_actual_owner_origins :
    NativeTables (T:=T) (v:=v) tags name (occurrencePageWord I)
      (projectOriginTape R.raw).result D.seats.result D.queries :=
  { side_matches := D.sideExact
    owner_hit := fun h=>by
      rw [D.ownerQuery h]
      exact project_roster_exact R tagLaw (owner v.parent.host.network h)
    owner_unique := fun h row found same=>by
      exact project_roster_unique R tagLaw inj (owner v.parent.host.network h) row found
        (same.trans (D.ownerQuery h))
    seat_hit := D.seatHit
    seat_unique := D.seatUnique }

def readBootAddon (h : (Port v.parent.host.Edge)) : Meter (Addon own (dim v) key prec page) :=
  witnessedReader (projectOriginTape R.raw).result D.seats.result D.queries D.fallback h

include tagLaw inj in
theorem read_boot_addon_exact (h : (Port v.parent.host.Edge)) :
    (readBootAddon D R h).result=addonAt T v name tags (occurrencePageWord I) h := by
  have hHit := no_raw_row_miss (T:=T) (v:=v) tags name (occurrencePageWord I)
    (projectOriginTape R.raw).result D.seats.result D.queries
    (compiled_input_reads_actual_owner_origins D R tagLaw inj) h
  simp only [readBootAddon,witnessedReader,hHit,Option.getD_some]

def measuredOriginSidecar : SiteInputs (compileOccurrence I) tags :=
  SiteInputs.fromReader (compileOccurrence I) tags name (occurrencePageWord I)
    (readBootAddon D R) (read_boot_addon_exact D R tagLaw inj)

variable (input : Meter (OccurrenceInput T v key prec tw bw page))
variable (source : Meter (CompleteRoster name value))
variable (B : BootPortWords input.result name)

def assembleOriginSite : Meter (StoredSite T v key prec tw bw page) :=
  let tape := projectOriginTape source.result.raw
  let read := witnessedReader tape.result B.seats.result B.queries B.fallback
  let occurrence := compileOccurrence input.result
  let emitted := emit read occurrence.native.physical.order
  let data : SiteInputs occurrence tags :=
    ⟨own,name,occurrencePageWord input.result,emitted.result,by
      exact (emit_exact read _).1.trans (List.map_congr_left
        (fun h _=>(read_boot_addon_exact B source.result tagLaw inj h)))⟩
  ⟨⟨input.result,tags,data,rfl⟩,input.steps+source.steps+B.seats.steps+tape.steps+emitted.steps⟩

theorem same_occurrence_and_paid_tag_sidecar :
    let A := assembleOriginSite tagLaw inj input source B
    A.result.input=input.result ∧ A.result.origins=tags ∧
    A.result.site.ownerWidth=own ∧
    A.result.site.install.result=some ((compileOccurrence input.result).native.physical.order.map
      (fun h=>⟨((compileOccurrence input.result).native.physical.record h).address,
        addonAt T v name tags (occurrencePageWord input.result) h⟩)) ∧
    A.steps=input.steps+source.steps+B.seats.steps+(projectOriginTape source.result.raw).steps+
      (emit (readBootAddon B source.result) (compileOccurrence input.result).native.physical.order).steps := by
  let side := measuredOriginSidecar B source.result tagLaw inj
  refine ⟨rfl,rfl,rfl,?_,rfl⟩
  exact side.install_exact.1

end
#print axioms compiled_input_reads_actual_owner_origins
#print axioms read_boot_addon_exact
#print axioms assembleOriginSite
#print axioms same_occurrence_and_paid_tag_sidecar
end J6R55TerminalOrigin
