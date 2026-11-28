import J6R33GeneratedChildSitePublish
import J6R33StatefulArithmeticPageWhole

/-! Compile a full hierarchy's occurrences from actual fixed-chart
metred resident artefacts. The compiler does not take a completed
OriginFields or a claimed runtime. Its resulting Birth is the one
consumed by the live R33 stateful arithmetic. -/
namespace J6R34RootAtlas
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R26DescriptorTree J6R24MeteredRecursion J6R12Blueprint J6R11Blueprint J6R10Reachable
open J6ActiveRun J6ActiveSchedule J6R9Recursive J1PPrinted J6R20Ancestor J6R10Repack
open J6R21Ancestor J6R32ChildResidentTransfer J6R16ModeCost J6R27OriginalGate J6R33GeneratedChildSite

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "positiveAt" => register_positive (ticketReady T ticket) ticket.centerAt

structure OccurrenceInput (T : Prepared cfg sel r hf) (ticket : Ticket sel r) (key prec tw bw page : ℕ) where
  port : ℕ
  edge : ℕ
  dep : ℕ
  tc : ℕ
  tz : ℕ
  tm : ℕ
  q : ℕ
  code : ℕ
  native : Meter (NativeJob T ticket port edge dep prec tc tz tm)
  issued : Meter (J6R15ModeCost.Word key)
  fw : List (A1R10.Word (registerPrecision SP ticket.parent ticket.centerAt))
  hOld : 0<fw.length
  hMod : A1R10.Modulus (registerPrecision SP ticket.parent ticket.centerAt)
    (register_positive (ticketReady T ticket) ticket.centerAt) fw=
      NativeProbeRing.liftPoly (registerPrecision SP ticket.parent ticket.centerAt) f
  physical : Meter (ChildResidents ((SP).levelBits ticket.parent.depth) q)
  geometry : ResidentReceipt (packing sel (ticketReady T ticket))
    (centerIndex (ticketReady T ticket) ticket.centerAt)
    (registerPrecision SP ticket.parent ticket.centerAt) physical.result
  words : Meter (ActiveWords fw (q+1) tw bw)
  group : words.result.group=native.result.gWord
  clock : words.result.axis.length=(centerIndex (ticketReady T ticket) ticket.centerAt).val
  centre : words.result.context.center=ticket.centerAt.val
  codeExact : words.result.context.codeWidth.val=code
  codePos : 0<code
  codeFit : 1+geometry.modes.length<2^code
  acted : words.result.exponents.map J6R15ModeCost.Word.val=geometry.modes.map
    (fun m=>siteTuple sel (ticketReady T ticket) ticket.slot.val
      ((packet_mode_equiv (packing sel (ticketReady T ticket)).mask
        (centerIndex (ticketReady T ticket) ticket.centerAt)
        (registerPrecision SP ticket.parent ticket.centerAt)).symm m))
  outerPos : 0<ell
  fit : (centerIndex (ticketReady T ticket) ticket.centerAt).val+1≤q+1
  probe : words.result.coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree
    (realProbeCount (S:=SP) (c:=ticket.parent)) (ticketReady T ticket).fit ticket.probeAt)
  width : (q-(SP).levelBits ticket.parent.depth)+13*(SP).levelBits ticket.parent.depth=page

theorem occurrence_real_receipt (I : OccurrenceInput T ticket key prec tw bw page) :
    Nonempty (AtlasReceipt (code:=I.code) I.geometry I.words.result positiveAt I.outerPos I.fit I.hMod
      (sampleNode SP f ell ticket.parent (ticketReady T ticket).fit ticket.centerAt ticket.probeAt)
      ticket.groupAt (activeMode sel (ticketReady T ticket) ticket.centerAt ticket.modeAt)) :=
  paid_native_occurrence_atlas I.geometry I.native.result I.words.result I.group I.clock I.centre I.codeExact
    I.codePos I.codeFit I.acted I.outerPos I.fit I.hMod I.probe

noncomputable def compileOccurrence (I : OccurrenceInput T ticket key prec tw bw page) :
    J6R33StatefulArithmeticPage.Birth T ticket key prec tw bw page :=
  let chosen := Classical.choice (occurrence_real_receipt I)
  let issued := padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  I.width ▸ issuedBirth I.native.result issued I.words.result I.hOld chosen


theorem transport_birth {uw vw : ℕ} (size : uw=vw)
    (b : J6R33StatefulArithmeticPage.Birth T ticket key prec tw bw uw) :
    let changed : J6R33StatefulArithmeticPage.Birth T ticket key prec tw bw vw := size ▸ b
    changed.job.identifier=b.job.identifier ∧
    changed.job.immutable.payload.stamp.created.val=b.job.immutable.payload.stamp.created.val ∧
    changed.issuance.steps=b.issuance.steps := by
  subst vw
  exact ⟨rfl,rfl,rfl⟩

theorem occurrence_identity (I : OccurrenceInput T ticket key prec tw bw page) :
    (compileOccurrence I).job.identifier=I.issued.result ∧
    (compileOccurrence I).job.immutable.payload.stamp.created.val=ticket.child.prec ∧
    (compileOccurrence I).issuance.steps=I.issued.steps+(I.native.steps+I.physical.steps+I.words.steps+4) := by
  let chosen := Classical.choice (occurrence_real_receipt I)
  let issued := padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  let b := issuedBirth I.native.result issued I.words.result I.hOld chosen
  have h := transport_birth I.width b
  exact ⟨h.1.trans b.tag.1,h.2.1.trans b.tag.2,h.2.2⟩

abbrev InputFamily (T : Prepared cfg sel r hf) (key prec tw bw page : ℕ) :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c),
    OccurrenceInput T (p.ticket w) key prec tw bw page

noncomputable def compileFamily (inputs : InputFamily T key prec tw bw page) :
    J6R33StatefulArithmeticPage.Births T key prec tw bw page :=
  fun p w=>compileOccurrence (inputs p w)

#print axioms occurrence_real_receipt
#print axioms compileOccurrence
#print axioms occurrence_identity
end J6R34RootAtlas
