import J6R52TerminalFreshBatch
import J6R34ChildPathReader
import J6R48LeafBirthRead

/-! The new raw command has the actual native Page value. There is
no assumption that the paid frame order equals the convention of a
classical finite enumeration. Any complete port order is legal. -/
namespace J6R52Terminal
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R26DescriptorTree J6R24MeteredRecursion J6R21Ancestor J6R20Ancestor
open J6R18ChildWrite J6R19Retained J6R22Active J6R27OriginalGate P1DyadicGrid P11FullPacking
open J6R32ChildResidentTransfer J6R32StatefulArithmetic J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open J6R34ChildPath J6R34RootAtlas J6R48Leaf J6R49SourceLayout J6R50Leaf J6R50SourceProducer J6R51Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 33500000
set_option maxRecDepth 4300

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)
local notation "SP" => printedParams (f:=f) (ell:=ell) s
local notation "aAt" => J6ActiveRun.Shape.levelBits SP (Call.depth (Ticket.parent v))
local notation "pAt" => stateWidth v
local notation "iAt" => axis T v
local notation "hpos" => register_positive (ticketReady T v) (Ticket.centerAt v)
local notation "βa" => activeMode sel (ticketReady T v) (Ticket.centerAt v) (Ticket.modeAt v)
variable {port edgeW dep prec tc tz tm q tw bw code key : ℕ}
variable {fw : List (A1R10.Word (stateWidth v))}
variable {R : ChildResidents ((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth) q}
variable {H : ResidentReceipt (layout T v) (axis T v) (stateWidth v) R}
variable {X : ActiveWords fw (q+1) tw bw}
variable {hv : 0<ell} {fit : (axis T v).val+1≤q+1}
variable {hMod : A1R10.Modulus (stateWidth v)
  (register_positive (ticketReady T v) v.centerAt) fw=NativeProbeRing.liftPoly (stateWidth v) f}

theorem physical_fresh_read_through_width
    (J : NativeJob T v port edgeW dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key)) (hOld : 0<fw.length)
    (A : AtlasReceipt (code:=code) H X hpos hv fit hMod (nativeProbe T v) v.groupAt βa)
    (k : PageAt T v) (hCentre : X.context.center=v.centerAt.val)
    (hCode : X.context.codeWidth.val=code) (codeFit : H.modes.length+1≤2^code)
    {page : ℕ} (width : (q-aAt)+13*aAt=page)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born
      ((width ▸ issuedBirth J issued X hOld A :
        J6R33StatefulArithmeticPage.Birth T v key prec tw bw page).job) path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened born rootLive path B)
    {current M : ℕ} (F : Frame f current)
    (ord : Fin M≃(bornPoint T v k).host.Edge) (bits : Fin M→Bool)
    (ports : List (PortAt (bornPoint T v k))) (all : ∀ u,u∈ports) :
    let issuedBirthAt : J6R33StatefulArithmeticPage.Birth T v key prec tw bw page :=
      width ▸ issuedBirth J issued X hOld A
    let cmd := ReadCmd.packet issuedBirthAt.job.identifier
      (width ▸ childPageKey (q-aAt) k : J6R15ModeCost.Word page) 0
      (ports.map (fun h=>⟨originSeed (layout T v) iAt v.groupAt k h,
        List.replicate (ord.symm (edge h.val)).val true⟩))
    F.decode (cmd.read hf F hv B (List.ofFn bits)).result=
      (entry (bornPoint T v k)).read hf current
        (assignment (bornPoint T v k).host.network (bits∘ord.symm) (bornPoint T v k).vertex) := by
  subst page
  let tr : Trace (bornPoint T v k) (bornPoint T v k) := .start
  let wired : List WireRead := ports.map (fun h=>⟨originSeed (layout T v) iAt v.groupAt k h,
        List.replicate (ord.symm (edge h.val)).val true⟩)
  exact (actual_issued_ancestor_read T v J issued hOld A k hCentre hCode codeFit
    path born wasBorn rootLive B live F tr ord bits ports all wired rfl).1

theorem real_compiled_fresh_read
    {page : ℕ} (I : OccurrenceInput T v key prec tw bw page)
    (k : PageAt T v)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born (compileOccurrence I).job path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened born rootLive path B)
    {current M : ℕ} (F : Frame f current)
    (ord : Fin M≃(bornPoint T v k).host.Edge) (bits : Fin M→Bool)
    (ports : List (PortAt (bornPoint T v k))) (all : ∀ u,u∈ports) :
    let cmd := ReadCmd.packet (compileOccurrence I).job.identifier
      (occurrencePageWord I k) 0
      (ports.map (fun h=>⟨originSeed (layout T v) iAt v.groupAt k h,
        List.replicate (ord.symm (edge h.val)).val true⟩))
    F.decode (cmd.read hf F I.outerPos B (List.ofFn bits)).result=
      (entry (bornPoint T v k)).read hf current
        (assignment (bornPoint T v k).host.network (bits∘ord.symm) (bornPoint T v k).vertex) :=
  physical_fresh_read_through_width T v I.native.result
    (A1R12.padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)) I.hOld
    (Classical.choice (occurrence_real_receipt I)) k I.centre I.codeExact
    (by simpa only [Nat.add_comm] using Nat.le_of_lt I.codeFit)
    I.width path born wasBorn rootLive B live F ord bits ports all

variable {T v}

def bornOrdinal {page : ℕ} (site : StoredSite T v key prec tw bw page) (k : PageAt T v) :
    Fin v.child.edges≃(bornPoint T v k).host.Edge :=
  (actualEdgeOrder T v site.birth.native.physical).trans (childHalves T v)

theorem emitted_fresh_word_reads_actual_page
    {page : ℕ} (site : StoredSite T v key prec tw bw page) (k : PageAt T v)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born site.birth.job path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened born rootLive path B)
    {current : ℕ} (F : Frame f current) (bits : Fin v.child.edges→Bool) :
    F.decode ((freshWord site k).read hf F site.input.outerPos B (List.ofFn bits)).result=
      (entry (bornPoint T v k)).read hf current
        (assignment (bornPoint T v k).host.network (bits∘(bornOrdinal site k).symm) (bornPoint T v k).vertex) := by
  have r := real_compiled_fresh_read T v site.input k path born wasBorn rootLive B live F
    (bornOrdinal site k) bits ((freshList site k).map asFreshPort) (fresh_list_complete site k)
  dsimp only at r
  rw [List.map_map] at r
  exact r

end
#print axioms physical_fresh_read_through_width
#print axioms real_compiled_fresh_read
#print axioms emitted_fresh_word_reads_actual_page
end J6R52Terminal
