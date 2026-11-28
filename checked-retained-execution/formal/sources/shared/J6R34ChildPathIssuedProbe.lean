import J6R34ChildPathOrigins
import J6R33GeneratedChildSitePublish
import J6R33StatefulArithmeticPageBoundRead

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 3400
set_option maxHeartbeats 2000000

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

theorem issued_probe_is_same_birth
    (A : AtlasReceipt (code:=code) H X hpos hv fit hMod (nativeProbe T v) v.groupAt βa)
    (k : PageAt T v) :
    letI := v.parent.host.finiteEdge
    letI := v.parent.host.finiteRow
    letI := v.parent.host.finiteCol
    bornPoint T v k=generatedPoint (layout T v) iAt (centerNonzero v.centerAt) rfl
      (castBox hMod (uvRead hpos fw ell (A.page k).fields.probe))
      v.parent.host.file (exponent T v) v.groupAt k := by
  letI := v.parent.host.finiteEdge
  letI := v.parent.host.finiteRow
  letI := v.parent.host.finiteCol
  have z : castBox hMod (uvRead hpos fw ell (A.page k).fields.probe)=nativeProbe T v :=
    (boxTransport_cast hMod _).symm.trans (A.page k).probe
  exact (actual_fresh_point T v k).trans
    (congrArg (fun x=>generatedPoint (layout T v) iAt (centerNonzero v.centerAt) rfl
      x v.parent.host.file (exponent T v) v.groupAt k) z.symm)

/-- Retargeting the trace at its actual delivered coefficient changes
neither the port fibre nor a single retained-prefix bit. Substitution
takes place in the runtime value, not in the large dependent receipt. -/
noncomputable def pointAtProbe (k : PageAt T v) (z : Residue f ell (stateWidth v)) : Point f ell := by
  letI := v.parent.host.finiteEdge
  letI := v.parent.host.finiteRow
  letI := v.parent.host.finiteCol
  exact generatedPoint (layout T v) iAt (centerNonzero v.centerAt) rfl z
    v.parent.host.file (exponent T v) v.groupAt k

theorem same_probe_keeps_exact_trace
    (k : PageAt T v) (z : Residue f ell (stateWidth v)) (hz : z=nativeProbe T v)
    {cur : Point f ell} (tr : Trace (bornPoint T v k) cur) :
    ∃ actual : Trace (pointAtProbe T v k z) cur, actual.depth=tr.depth ∧
      ∀ u : PortAt cur,actual.literal (originSeed (layout T v) iAt v.groupAt k) u=
        tr.literal (originSeed (layout T v) iAt v.groupAt k) u := by
  subst z
  exact ⟨tr,rfl,fun _=>rfl⟩

#print axioms issued_probe_is_same_birth
#print axioms same_probe_keeps_exact_trace
end J6R34ChildPath
