import J6R66LeafTariffNumbers
import J6R65LeafRateEntry
import J6R58LeafScaleNative
import J6R48LeafBirthFormat

/-! The measured reader points at its actual ancestor occurrence and
physical page. The public-width transport changes only the address
type, not the number of rows, modes, or creation-time precision. -/
namespace J6R66LeafTariff
open scoped Polynomial Classical
open AOracleMachineTime A1R12 J6R21Ancestor J6R18ChildWrite J6R32ChildResidentTransfer
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R34RootAtlas J6R32StatefulArithmetic
open J6R33GeneratedChildSite J6R24MeteredRecursion J6R48Leaf
open J6ActiveRun J6ActiveSchedule J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R58LeafScale J6R65LeafRate J6R16ModeCost J6R26DescriptorTree J6R27OriginalGate
open P11FullPacking J6R10Repack J6R22Active J6R10Reachable J6R49SourceLayout J6R9Recursive

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 27000000
set_option maxRecDepth 4200
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c target : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "axisAt" => (SP).levelBits v.parent.depth
local notation "realPage" => Page axisAt (packing sel (ticketReady T v)).copies (Fin 64)

def nativePageWord (I : OccurrenceInput T v key prec tw bw page) (k : realPage) :
    J6R15ModeCost.Word page :=
  occurrencePageWord I k

/-- A generic equality transport for the actual publication. The packet
contents are kept definitionally when the common width equals its native width. -/
private theorem issued_width_preserves_payload
    {port edgeW dep tc tz tm q code : ℕ}
    {fw : List (A1R10.Word (registerPrecision SP v.parent v.centerAt))}
    {R : ChildResidents axisAt q}
    {H : ResidentReceipt (packing sel (ticketReady T v)) (centerIndex (ticketReady T v) v.centerAt)
      (registerPrecision SP v.parent v.centerAt) R}
    {X : ActiveWords fw (q+1) tw bw}
    {hp : 0<ell} {fit : (centerIndex (ticketReady T v) v.centerAt).val+1≤q+1}
    {hMod : A1R10.Modulus (registerPrecision SP v.parent v.centerAt)
      (register_positive (ticketReady T v) v.centerAt) fw=
        NativeProbeRing.liftPoly (registerPrecision SP v.parent v.centerAt) f}
    (J : NativeJob T v port edgeW dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key)) (hOld : 0<fw.length)
    (A : AtlasReceipt (code:=code) H X (register_positive (ticketReady T v) v.centerAt) hp fit hMod
      (sampleNode SP f ell v.parent (ticketReady T v).fit v.centerAt v.probeAt) v.groupAt
      (activeMode sel (ticketReady T v) v.centerAt v.modeAt))
    (width : (q-axisAt)+13*axisAt=page) (k : realPage) :
    let Q : J6R33StatefulArithmeticPage.Birth T v key prec tw bw page :=
      width ▸ issuedBirth J issued X hOld A
    let selector : J6R15ModeCost.Word page := width ▸ childPageKey (q-axisAt) k
    let record := Q.job.immutable.payload
    ∃ F : pageFields record,
      (locate selector record.payload.pages).result=some F ∧
      F.rows.length=(A.page k).fields.rows.length ∧
      F.cols.length=(A.page k).fields.cols.length ∧
      F.modes.length=(A.page k).fields.modes.length ∧
      record.payload.shape.a=axisAt ∧ record.payload.shape.p=registerPrecision SP v.parent v.centerAt := by
  subst page
  exact ⟨(A.page k).fields,A.lookup k,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_ancestor_page_has_printed_dimensions (par : Path sel r c) (slot : (Plan sel).Slot c)
    (I : OccurrenceInput T (par.ticket slot) key prec tw bw page)
    (k : Page ((SP).levelBits c.depth) (packing sel (ticketReady T (par.ticket slot))).copies (Fin 64)) :
    let record := (compileOccurrence I).job.immutable.payload
    ∃ F : pageFields record,
      (locate (nativePageWord I k) record.payload.pages).result=some F ∧
      record.payload.shape.a=stepA (Nat.clog 2 s) c.depth ∧
      record.payload.shape.p≤r.prec+160*C*s^2 ∧
      F.rows.length≤2^record.payload.shape.a ∧
      F.cols.length≤2^record.payload.shape.a ∧
      F.modes.length≤3*(C*s)*record.payload.shape.p := by
  let A := chosenAtlas I
  let Q := (compileOccurrence I).job.immutable.payload
  obtain ⟨data,hit,rows,cols,modes,axis,prec⟩ :=
    issued_width_preserves_payload I.native.result
      (padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)) I.hOld A I.width k
  have geom := actual_occurrence_compact_chart par slot I
  refine ⟨data,hit,axis,?_,?_,?_,?_⟩
  · exact prec.trans_le geom.2.1
  · exact rows.trans_le ((geom.2.2 k).1.trans_eq (congrArg (fun a : ℕ=>2^a) axis.symm))
  · exact cols.trans_le ((geom.2.2 k).2.1.trans_eq (congrArg (fun a : ℕ=>2^a) axis.symm))
  · exact modes.trans_le ((geom.2.2 k).2.2.trans_eq (congrArg (fun p=>3*(C*s)*p) prec.symm))

/-- The bound prices a reached physical ancestor page under exactly
the live raw reader used by the leaf. No whole-reader cap is assumed.
Source base width plus the exterior creation reserve implies the start
precision used here; the register never gets reset at the exterior. -/
theorem actual_reached_ancestor_reader_geometric
    (par : Path sel r c) (slot : (Plan sel).Slot c)
    (I : OccurrenceInput T (par.ticket slot) key prec tw bw page)
    (k : Page ((SP).levelBits c.depth) (packing sel (ticketReady T (par.ticket slot))).copies (Fin 64))
    (path : Path sel r target) (born : Births T key prec tw bw page)
    (used : OnPath born (compileOccurrence I).job path)
    (origin : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (running : opened born origin path B)
    (rootPrecision : r.prec≤161*C*s^2) {e p edges : ℕ}
    (dep : ℕ) (wires : List WireRead) :
    let job := (compileOccurrence I).job
    let record := job.immutable.payload
    ∃ F : pageFields record,(locate (nativePageWord I k) record.payload.pages).result=some F ∧
      rawPageFee e p edges B (.generated job.identifier (nativePageWord I k) dep wires)≤
        2^(6*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))*actualPacketPrefactor B record F p dep wires := by
  let job := (compileOccurrence I).job
  let record := job.immutable.payload
  obtain ⟨fld,hit,a,hPrec,rows,_,modes⟩ := actual_ancestor_page_has_printed_dimensions par slot I k
  have width : record.payload.shape.p≤321*C*s^2 := by
    calc
      _≤r.prec+160*C*s^2 := hPrec
      _≤161*C*s^2+160*C*s^2 := Nat.add_le_add_right rootPrecision _
      _=_ := by ring
  have large := root_lambda_large cfg
  have count := native_mode_count_at_absolute_receiver large cfg.constSmall width modes
  have alive : IsLive job B := ancestor_paged_live born job path used B running
  exact ⟨fld,hit,found_generated_reader_rate_from_created_page_dimensions B record fld job.identifier
    (nativePageWord I k) alive.2 hit s c.depth large a rows count e p edges dep wires⟩

#print axioms nativePageWord
#print axioms actual_ancestor_page_has_printed_dimensions
#print axioms actual_reached_ancestor_reader_geometric
end
end J6R66LeafTariff
