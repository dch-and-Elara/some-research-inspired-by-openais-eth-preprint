import J6R49LeafOriginal
import J6R48LeafBirthRead
import J6R34RootAtlasOccurrence

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24500000
set_option maxRecDepth 3700

/-! A complete row recipe for one prior native call. The R34 compiled
occurrence may transport its Page-key width, but the underlying actual
atlas, probe, creator record, and read never get reconstructed from an
unrelated statement or numeric value. -/
namespace J6R49Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R26DescriptorTree J6R24MeteredRecursion J6R21Ancestor J6R20Ancestor
open J6R18ChildWrite J6R19Retained J6R22Active J6R27OriginalGate P1DyadicGrid P11FullPacking
open J6R32ChildResidentTransfer J6R32StatefulArithmetic J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open J6R34ChildPath J6R34RootAtlas J6R48Leaf

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

def nativeRowTransported
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
    (F : Frame f c.prec) (pos : 0<ell) (vertex : Vertex c)
    (tr : Trace (bornPoint T v k) (atVertex c vertex)) (ord : Fin c.edges≃c.host.Edge) :
    RowAt hf F pos ord vertex (opened born rootLive path) := by
  subst page
  let w := literalWires vertex tr (originSeed (layout T v) iAt v.groupAt k) ord
  let Q := issuedBirth J issued X hOld A
  refine ⟨PageReadCode.generated Q.job.identifier (childPageKey (q-aAt) k) tr.depth w,?_,?_⟩
  · intro B good bits
    exact (issued_native_leaf_entry_value_and_fee T v J issued hOld A k hCentre hCode codeFit path
      born wasBorn rootLive B good F vertex tr ord bits (portList vertex)
      (portList_complete vertex) w rfl).1
  · intro B good
    exact issued_atlas_is_resident_read_format T v J issued hOld A k hCentre hCode codeFit path
      born wasBorn rootLive B good tr.depth w

def fromCompiledOccurrence {page : ℕ}
    (I : OccurrenceInput T v key prec tw bw page) (k : PageAt T v)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born (compileOccurrence I).job path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (F : Frame f c.prec) (pos : 0<ell) (vertex : Vertex c)
    (tr : Trace (bornPoint T v k) (atVertex c vertex)) (ord : Fin c.edges≃c.host.Edge) :
    RowAt hf F pos ord vertex (opened born rootLive path) :=
  nativeRowTransported T v I.native.result
    (padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)) I.hOld
    (Classical.choice (occurrence_real_receipt I)) k I.centre I.codeExact (by simpa only [Nat.add_comm] using Nat.le_of_lt I.codeFit)
    I.width path born wasBorn rootLive F pos vertex tr ord

#print axioms nativeRowTransported
#print axioms fromCompiledOccurrence
end
end J6R49Leaf
