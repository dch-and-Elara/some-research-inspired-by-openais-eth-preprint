import J6R52TerminalFreshBatch
import J6R34ChildPathReader
import J6R48LeafBirthRead

/-! Evaluating a descendant's command uses its original ancestor's
actual padded acquisition, not a separately supplied probe or old
coefficient table. The true port trace may have arbitrary depth. -/
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

theorem physical_inherited_read_through_width
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
    {current M : ℕ} (F : Frame f current) {cur : Point f ell}
    (trace : Trace (bornPoint T v k) cur)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool)
    (ports : List (PortAt cur)) (all : ∀ u,u∈ports)
    (wires : List WireRead)
    (raw : wires=ports.map (fun h=>⟨trace.literal (originSeed (layout T v) iAt v.groupAt k) h,
        List.replicate (ord.symm (edge h.val)).val true⟩)) :
    let issuedBirthAt : J6R33StatefulArithmeticPage.Birth T v key prec tw bw page :=
      width ▸ issuedBirth J issued X hOld A
    let cmd := ReadCmd.packet issuedBirthAt.job.identifier
      (width ▸ childPageKey (q-aAt) k : J6R15ModeCost.Word page) trace.depth wires
    F.decode (cmd.read hf F hv B (List.ofFn bits)).result =
      (entry cur).read hf current (assignment cur.host.network (bits∘ord.symm) cur.vertex) := by
  subst page
  exact (actual_issued_ancestor_read T v J issued hOld A k hCentre hCode codeFit
    path born wasBorn rootLive B live F trace ord bits ports all wires raw).1

theorem real_compiled_inherited_read
    {page : ℕ} (I : OccurrenceInput T v key prec tw bw page)
    (k : PageAt T v)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born (compileOccurrence I).job path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened born rootLive path B)
    {current M : ℕ} (F : Frame f current) {cur : Point f ell}
    (trace : Trace (bornPoint T v k) cur)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool)
    (ports : List (PortAt cur)) (all : ∀ u,u∈ports) :
    let cmd := ReadCmd.packet (compileOccurrence I).job.identifier
      (occurrencePageWord I k) trace.depth
      (ports.map (fun h=>⟨trace.literal (originSeed (layout T v) iAt v.groupAt k) h,
        List.replicate (ord.symm (edge h.val)).val true⟩))
    F.decode (cmd.read hf F I.outerPos B (List.ofFn bits)).result=
      (entry cur).read hf current (assignment cur.host.network (bits∘ord.symm) cur.vertex) :=
  physical_inherited_read_through_width T v I.native.result
    (A1R12.padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)) I.hOld
    (Classical.choice (occurrence_real_receipt I)) k I.centre I.codeExact
    (by simpa only [Nat.add_comm] using Nat.le_of_lt I.codeFit)
    I.width path born wasBorn rootLive B live F trace ord bits ports all _ rfl

end
#print axioms physical_inherited_read_through_width
#print axioms real_compiled_inherited_read
end J6R52Terminal
