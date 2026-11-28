import J6R33GeneratedChildSiteSource
import J6R33StatefulArithmeticPagePath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2700
set_option maxHeartbeats 17500000

/-! Direct native Birth binding for the stateful interpreter.
The chronological ID and receiving precision come from the actual
descriptor issuer. No second mode/page table is passed to the gate. -/
namespace J6R33GeneratedChildSite
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage
open J6R26DescriptorTree J6R24MeteredRecursion J6R12Blueprint J6R11Blueprint J6R10Reachable
open J6ActiveRun J6R9Recursive J1PPrinted J6R20Ancestor
open J6R21Ancestor J6R32ChildResidentTransfer J6R16ModeCost J6R27OriginalGate

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep prec tc tz tm q tw bw code key : ℕ}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "aAt" => J6ActiveRun.Shape.levelBits SP ticket.parent.depth
local notation "iAt" => centerIndex (ticketReady T ticket) ticket.centerAt
local notation "pAt" => registerPrecision SP ticket.parent ticket.centerAt
local notation "kAt" => ((q-aAt)+13*aAt)
local notation "hp" => register_positive (ticketReady T ticket) ticket.centerAt
local notation "node" => sampleNode SP f ell ticket.parent (Ready.fit (ticketReady T ticket)) ticket.centerAt ticket.probeAt
local notation "beta" => activeMode sel (ticketReady T ticket) ticket.centerAt ticket.modeAt
variable {fw : List (A1R10.Word (registerPrecision (printedParams (f:=f) (ell:=ell) s)
    ticket.parent ticket.centerAt))}
variable {R : ChildResidents ((printedParams (f:=f) (ell:=ell) s).levelBits ticket.parent.depth) q}
variable {H : ResidentReceipt (packing sel (ticketReady T ticket))
    (centerIndex (ticketReady T ticket) ticket.centerAt)
    (registerPrecision (printedParams (f:=f) (ell:=ell) s) ticket.parent ticket.centerAt) R}

def issuedBirth
    (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key))
    (X : ActiveWords fw (q+1) tw bw) (hOld : 0<fw.length)
    {hv : 0<ell} {fit : (iAt).val+1≤q+1}
    {hMod : A1R10.Modulus pAt hp fw=NativeProbeRing.liftPoly pAt f}
    (A : AtlasReceipt (code:=code) H X hp hv fit hMod node ticket.groupAt beta) :
    Birth T ticket key prec tw bw kAt where
  port := port
  edge := edge
  dep := dep
  tc := tc
  tz := tz
  tm := tm
  native := J
  issuance := issued
  ctx := X.context
  shape := issuedFrame (q:=q) J fw hOld hMod
  actualPrec := rfl
  compilePages := runSiteRows (code:=code) R X hp hv fit
  rows := A.bank
  success := A.rowsReady
  keysUnique := A.keysUnique

theorem priced_birth_by_actual_page
    (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key))
    (X : ActiveWords fw (q+1) tw bw) (hOld : 0<fw.length)
    {hv : 0<ell} {fit : (iAt).val+1≤q+1}
    {hMod : A1R10.Modulus pAt hp fw=NativeProbeRing.liftPoly pAt f}
    (A : AtlasReceipt (code:=code) H X hp hv fit hMod node ticket.groupAt beta) :
    let born := issuedBirth J issued X hOld A
    born.job.identifier=issued.result ∧
      born.job.immutable.payload.stamp.created.val=ticket.child.prec ∧
      (∀ k,(locate (childPageKey (q-aAt) k) born.rows).result=some (A.page k).fields) ∧
      born.compilePages.steps≤runFee (ell:=ell) (code:=code) (tw:=tw) (bw:=bw) (fw:=fw) H+3 := by
  let born := issuedBirth J issued X hOld A
  exact ⟨born.tag.1,born.tag.2,A.lookup,A.rowsFee⟩

theorem actual_child_occurrence_birth
    (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key))
    (X : ActiveWords fw (q+1) tw bw) (hG : X.group=J.gWord)
    (clock : X.axis.length=(iAt).val)
    (hCentre : X.context.center=ticket.centerAt.val) (hCode : X.context.codeWidth.val=code)
    (codePos : 0<code) (codeFit : 1+H.modes.length<2^code)
    (hβ : X.exponents.map J6R15ModeCost.Word.val=H.modes.map
      (fun m=>siteTuple sel (ticketReady T ticket) ticket.slot.val
        ((packet_mode_equiv (packing sel (ticketReady T ticket)).mask iAt pAt).symm m)))
    (hv : 0<ell) (fit : (iAt).val+1≤q+1) (hOld : 0<fw.length)
    (hMod : A1R10.Modulus pAt hp fw=NativeProbeRing.liftPoly pAt f)
    (hZ : X.coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree
      (realProbeCount (S:=SP) (c:=ticket.parent)) (ticketReady T ticket).fit ticket.probeAt)) :
    ∃ A : AtlasReceipt (code:=code) H X hp hv fit hMod node ticket.groupAt beta,
      let born := issuedBirth J issued X hOld A
      born.job.identifier=issued.result ∧
      born.job.immutable.payload.stamp.created.val=ticket.child.prec ∧
      born.shape.birth=J.receiving ∧
      born.ctx.center=ticket.centerAt.val ∧ born.ctx.codeWidth.val=code ∧
      (∀ k,(locate (childPageKey (q-aAt) k) born.rows).result=some (A.page k).fields) ∧
      born.compilePages.steps≤runFee (ell:=ell) (code:=code) (tw:=tw) (bw:=bw) (fw:=fw) H+3 := by
  obtain ⟨A⟩ := paid_native_occurrence_atlas H J X hG clock hCentre hCode codePos codeFit hβ hv fit hMod hZ
  have E := priced_birth_by_actual_page J issued X hOld A
  exact ⟨A,E.1,E.2.1,rfl,hCentre,hCode,E.2.2.1,E.2.2.2⟩

#print axioms issuedBirth
#print axioms priced_birth_by_actual_page
#print axioms actual_child_occurrence_birth
end J6R33GeneratedChildSite
