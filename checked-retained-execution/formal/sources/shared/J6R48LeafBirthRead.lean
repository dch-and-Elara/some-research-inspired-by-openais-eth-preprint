import J6R48LeafBirthFormat
import J6R34ChildPathReader

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 3750

/-! Exact native generated entry coupled to the R48 raw local fee.
The immutable record is from the addressed actual creator and actual
page of the same ancestor slot; the current assignment is the literal
source leaf edge order. No caller-provided numeric truth or fee. -/
namespace J6R48Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R26DescriptorTree J6R24MeteredRecursion J6R21Ancestor J6R20Ancestor
open J6R18ChildWrite J6R19Retained J6R22Active J6R27OriginalGate P1DyadicGrid P11FullPacking
open J6R32ChildResidentTransfer J6R32StatefulArithmetic
open J6R33GeneratedChildSite J6R33StatefulArithmeticPage J6R34ChildPath

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

theorem issued_native_leaf_entry_value_and_fee
    (J : NativeJob T v port edgeW dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key)) (hOld : 0<fw.length)
    (A : AtlasReceipt (code:=code) H X hpos hv fit hMod (nativeProbe T v) v.groupAt βa)
    (k : PageAt T v) (hCentre : X.context.center=v.centerAt.val)
    (hCode : X.context.codeWidth.val=code) (codeFit : H.modes.length+1≤2^code)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw ((q-aAt)+13*aAt))
    (wasBorn : OnPath born (issuedBirth J issued X hOld A).job path)
    (rootLive : PageBank f ell key prec tw bw ((q-aAt)+13*aAt)→Prop)
    (B : PageBank f ell key prec tw bw ((q-aAt)+13*aAt)) (live : opened born rootLive path B)
    (F : Frame f c.prec) (vertex : c.host.Row⊕c.host.Col)
    (tr : Trace (bornPoint T v k) (point c.host vertex))
    (ord : Fin c.edges≃c.host.Edge) (bits : Fin c.edges→Bool)
    (ports : List (PortAt (point c.host vertex))) (hall : ∀ u,u∈ports)
    (wires : List WireRead)
    (raw : wires=ports.map (fun u=>⟨tr.literal
      (originSeed (layout T v) iAt v.groupAt k) u,
      List.replicate (ord.symm (J6R10Repack.edge u.val)).val true⟩)) :
    let Q := issuedBirth J issued X hOld A
    let cmd := PageReadCode.generated (edges:=c.edges) Q.job.identifier (childPageKey (q-aAt) k) tr.depth wires
    let read := cmd.run hf F hv B (List.ofFn bits)
    F.decode read.result=(c.host.file vertex).read hf c.prec
      (assignment c.host.network (bits∘ord.symm) vertex) ∧
      (c.host.file vertex).created=v.child.prec ∧
      read.steps≤rawPageFee F.words.length c.prec c.edges B cmd := by
  have Hform := issued_atlas_is_resident_read_format T v J issued hOld A k hCentre hCode codeFit
    path born wasBorn rootLive B live tr.depth wires
  obtain ⟨value,tag⟩ := actual_issued_ancestor_read T v J issued hOld A k hCentre hCode codeFit
    path born wasBorn rootLive B live F tr ord bits ports hall wires raw
  exact ⟨value,tag,raw_paged_read_bound hf F hv B _ Hform (List.ofFn bits) List.length_ofFn⟩

#print axioms issued_native_leaf_entry_value_and_fee
end J6R48Leaf
