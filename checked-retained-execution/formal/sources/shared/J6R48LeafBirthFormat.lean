import J6R48LeafRawReader
import J6R33GeneratedChildSitePublish

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16500000
set_option maxRecDepth 3000

/-! Derive the R48 checkable read format for an actual native child
occurrence and a specific paid Page of its original atlas. Older
occurrences can intervene in the bank, but no arbitrary address,
probe, shape, dimensions, or reconstructed value is accepted. -/
namespace J6R48Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R26DescriptorTree J6R24MeteredRecursion J6R21Ancestor J6R20Ancestor
open J6R18ChildWrite J6R19Retained J6R22Active J6R27OriginalGate P1DyadicGrid P11FullPacking
open J6R32ChildResidentTransfer J6R32StatefulArithmetic J6R30ProducedGateRegistry
open J6R33GeneratedChildSite J6R33StatefulArithmeticPage

theorem list_modes_have_source_codes {a p w n : ℕ} {i : Fin a}
    (ms : Fin n→ModeInput a p i w) (b : ℕ)
    (codes : ∀ j,(ms j).code=encodeBits b j.succ.val)
    (l : List (ModeInput a p i w)) (eq : l=List.ofFn ms) :
    ∀ j : Fin l.length,(l.get j).code=encodeBits b j.succ.val := by
  subst l
  intro j
  have h : j.val<n := by simpa only [List.length_ofFn] using j.isLt
  exact (congrArg ModeInput.code (List.get_ofFn ms j)).trans (codes ⟨j.val,h⟩)

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

local notation "SP" => printedParams (f:=f) (ell:=ell) s
local notation "aAt" => J6ActiveRun.Shape.levelBits SP (Call.depth (Ticket.parent v))
local notation "pAt" => registerPrecision SP v.parent v.centerAt
local notation "iAt" => centerIndex (ticketReady T v) v.centerAt
local notation "hpos" => register_positive (ticketReady T v) v.centerAt
local notation "βa" => activeMode sel (ticketReady T v) v.centerAt v.modeAt
local notation "node" => sampleNode SP f ell v.parent (Ready.fit (ticketReady T v)) v.centerAt v.probeAt

variable {port edgeW dep prec tc tz tm q tw bw code key : ℕ}
variable {fw : List (A1R10.Word (registerPrecision (printedParams (f:=f) (ell:=ell) s)
    v.parent v.centerAt))}
variable {R : ChildResidents ((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth) q}
variable {H : ResidentReceipt (packing sel (ticketReady T v))
  (centerIndex (ticketReady T v) v.centerAt)
  (registerPrecision (printedParams (f:=f) (ell:=ell) s) v.parent v.centerAt) R}
variable {X : ActiveWords fw (q+1) tw bw}
variable {hv : 0<ell} {fit : (centerIndex (ticketReady T v) v.centerAt).val+1≤q+1}
variable {hMod : A1R10.Modulus (registerPrecision (printedParams (f:=f) (ell:=ell) s) v.parent v.centerAt)
  (register_positive (ticketReady T v) v.centerAt) fw=
    NativeProbeRing.liftPoly (registerPrecision (printedParams (f:=f) (ell:=ell) s) v.parent v.centerAt) f}
local notation "pgWidth" => (q-aAt)+13*aAt
local notation "L" => PageBank f ell key prec tw bw pgWidth

theorem issued_atlas_is_resident_read_format
    (J : NativeJob T v port edgeW dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key)) (hOld : 0<fw.length)
    (A : AtlasReceipt (code:=code) H X hpos hv fit hMod node v.groupAt βa)
    (k : Page aAt (packing sel (ticketReady T v)).copies (Fin 64))
    (hCentre : X.context.center=v.centerAt.val) (hCode : X.context.codeWidth.val=code)
    (codeFit : H.modes.length+1≤2^code)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw pgWidth)
    (wasBorn : OnPath born (issuedBirth J issued X hOld A).job path)
    (rootLive : L→Prop) (B : L) (live : opened born rootLive path B)
    (retention : ℕ) (wires : List WireRead) :
    ResidentReadForm B (PageReadCode.generated (edges:=c.edges)
      (issuedBirth J issued X hOld A).job.identifier (childPageKey (q-aAt) k) retention wires) := by
  let Q := issuedBirth J issued X hOld A
  let record := Q.job.immutable.payload
  let field : pageFields record := (A.page k).fields
  have found : (locate Q.job.identifier B.records).result=some record :=
    (ancestor_paged_live born Q.job path wasBorn B live).2
  have pageHit : (locate (childPageKey (q-aAt) k) record.payload.pages).result=some field :=
    A.lookup k
  refine ⟨record,found,rfl,rfl,field,pageHit,?_⟩
  refine ⟨?_,Nat.succ_pos q,?_,?_,?_⟩
  · change X.context.center∈P1DyadicGrid.grid aAt
    rw [hCentre]
    exact (active_grid _ _ _ v.centerAt.property).1
  · change (A.page k).fields.modes.length+1≤2^X.context.codeWidth.val
    rw [(A.page k).modeList,List.length_ofFn,hCode]
    exact codeFit
  · change (A.page k).fields.rows.length<2^(q+1)
    rw [(A.page k).rowSlots,List.length_map]
    exact rows_fit_word H v.groupAt k
  · change ∀ j : Fin (A.page k).fields.modes.length,
      ((A.page k).fields.modes.get j).code=encodeBits X.context.codeWidth.val j.succ.val
    rw [hCode]
    exact list_modes_have_source_codes (A.page k).modes code (A.page k).modeCodes
      (A.page k).fields.modes (A.page k).modeList

#print axioms list_modes_have_source_codes
#print axioms issued_atlas_is_resident_read_format
end J6R48Leaf
