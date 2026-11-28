import J6R34ChildPathIssuedProbe
import J6R33StatefulArithmeticPageBoundRead

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 3400
set_option maxHeartbeats 5500000

/-! No supplied equality between a birth capsule and some purported
origin point. Its actual paid probe is proved to give the same point
created by the native slot, and the exact bank record supplies all
typed R27 arguments of the real inherited reader. -/
namespace J6R34ChildPath
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R26DescriptorTree J6R24MeteredRecursion J6R21Ancestor J6R20Ancestor
open J6R18ChildWrite J6R19Retained J6R22Active J6R27OriginalGate P1DyadicGrid P11FullPacking
open J6R32ChildResidentTransfer J6R32StatefulArithmetic
open J6R33GeneratedChildSite J6R33StatefulArithmeticPage

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

theorem actual_issued_ancestor_read
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
    {current M : ℕ} (F : Frame f current) {cur : Point f ell}
    (tr : Trace (bornPoint T v k) cur)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool) (ports : List (PortAt cur)) (hall : ∀ u,u∈ports)
    (wires : List WireRead)
    (raw : wires=ports.map (fun u=>⟨tr.literal
      (originSeed (layout T v) iAt v.groupAt k) u,
      List.replicate (ord.symm (J6R10Repack.edge u.val)).val true⟩)) :
    let Q := issuedBirth J issued X hOld A
    let pg := childPageKey (q-aAt) k
    let run := (PageReadCode.generated (edges:=M) Q.job.identifier pg tr.depth wires).run hf F hv B
      (List.ofFn bits)
    F.decode run.result=(entry cur).read hf current
      (assignment cur.host.network (bits∘ord.symm) cur.vertex) ∧
      (entry cur).created=v.child.prec := by
  letI := v.parent.host.finiteEdge
  letI := v.parent.host.finiteRow
  letI := v.parent.host.finiteCol
  let Q := issuedBirth J issued X hOld A
  let C := A.page k
  let z := castBox hMod (uvRead hpos fw ell C.fields.probe)
  have view : z=nativeProbe T v := (boxTransport_cast hMod _).symm.trans C.probe
  obtain ⟨actualTrace,depEqual,lit⟩ := same_probe_keeps_exact_trace T v k z view tr
  have rawE : wires=ports.map (fun u=>⟨actualTrace.literal
      (originSeed (layout T v) iAt v.groupAt k) u,
      List.replicate (ord.symm (J6R10Repack.edge u.val)).val true⟩) := by
    refine raw.trans (List.map_congr_left (fun u _=>?_))
    rw [lit u]
  have ht : v.centerAt.val∈grid aAt := (active_grid _ _ _ v.centerAt.property).1
  obtain ⟨value,tag,_fee⟩ :=
    actual_inherited_page_port Q F hv (layout T v) ht (centerNonzero v.centerAt) rfl
      v.parent.host.file v.groupAt k ((RosterIndex H).trans (packet_mode_equiv (layout T v).mask iAt pAt).symm)
      (exponent T v) C.modes C.modeMeaning
      (sourceRows (layout T v) iAt v.groupAt k H.edges) C.rowsUnique C.allRows
      (sourceCols (layout T v) iAt v.groupAt k H.edges) C.colsUnique C.allCols
      code (Nat.succ_pos q) codeFit (rows_fit_word H v.groupAt k) C.modeCodes B born path
      wasBorn rootLive live (childPageKey (q-aAt) k) C.fields (A.lookup k)
      hCentre hCode C.rowSlots C.colSlots C.modeList actualTrace ord bits ports hall wires rawE
  change F.decode ((PageReadCode.generated (edges:=M) Q.job.identifier (childPageKey (q-aAt) k)
    actualTrace.depth wires).run hf F hv B (List.ofFn bits)).result=_ at value
  rw [depEqual] at value
  exact ⟨value,tag⟩

#print axioms actual_issued_ancestor_read
end J6R34ChildPath
