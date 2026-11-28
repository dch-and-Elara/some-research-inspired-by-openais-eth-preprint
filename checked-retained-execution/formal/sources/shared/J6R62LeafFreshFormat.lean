import J6R62LeafTerminal
import J6R48LeafBirthFormat

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 33500000
set_option maxRecDepth 4200

/-! The current fresh atlas needs no assumed fee or packet format.
Transport the genuine R48 issued atlas through its actual page-width
cast before forming the R53/R57 terminal command. -/
namespace J6R62Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R26DescriptorTree J6R24MeteredRecursion J6R21Ancestor J6R20Ancestor
open J6R18ChildWrite J6R19Retained J6R22Active J6R27OriginalGate P1DyadicGrid P11FullPacking
open J6R32ChildResidentTransfer J6R32StatefulArithmetic J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open J6R34ChildPath J6R34RootAtlas J6R48Leaf J6R49SourceLayout J6R50Leaf J6R50SourceProducer
open J6R51Leaf J6R52Terminal

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

section Transport
variable {port edgeW dep prec tc tz tm q tw bw code key : ℕ}
variable {fw : List (A1R10.Word (stateWidth v))}
variable {R : ChildResidents ((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth) q}
variable {H : ResidentReceipt (layout T v) (axis T v) (stateWidth v) R}
variable {X : ActiveWords fw (q+1) tw bw}
variable {hv : 0<ell} {fit : (axis T v).val+1≤q+1}
variable {hMod : A1R10.Modulus (stateWidth v) (register_positive (ticketReady T v) v.centerAt) fw=NativeProbeRing.liftPoly (stateWidth v) f}

theorem actual_format_in_native_or_printed_width
    (J : NativeJob T v port edgeW dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key)) (hOld : 0<fw.length)
    (A : AtlasReceipt (code:=code) H X (register_positive (ticketReady T v) v.centerAt) hv fit hMod (nativeProbe T v) v.groupAt (activeMode sel (ticketReady T v) v.centerAt v.modeAt))
    (k : PageAt T v) (hCentre : X.context.center=v.centerAt.val)
    (hCode : X.context.codeWidth.val=code) (codeFit : H.modes.length+1≤2^code)
    {page : ℕ} (width : (q-((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth))+13*((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth)=page)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born
      ((width ▸ issuedBirth J issued X hOld A :
        J6R33StatefulArithmeticPage.Birth T v key prec tw bw page).job) path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened born rootLive path B)
    (edges retention : ℕ) (wires : List WireRead) :
    let publication : J6R33StatefulArithmeticPage.Birth T v key prec tw bw page := width ▸ issuedBirth J issued X hOld A
    ReadFormat B edges (.packet publication.job.identifier
      (width ▸ childPageKey (q-((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth)) k : J6R15ModeCost.Word page) retention wires) := by
  subst page
  exact issued_atlas_is_resident_read_format T v J issued hOld A k hCentre hCode codeFit
    path born wasBorn rootLive B live retention wires
end Transport

variable {key prec tw bw page : ℕ}

theorem actual_compiled_atlas_read_formats
    (site : StoredSite T v key prec tw bw page)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born site.birth.job path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened born rootLive path B)
    (edges : ℕ) (cmd : ReadCmd key page)
    (onAtlas : cmd∈(trueFreshPages site).map (freshWord site)) :
    ReadFormat B edges cmd := by
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp onAtlas
  let I := site.input
  exact actual_format_in_native_or_printed_width I.native.result
    (A1R12.padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)) I.hOld
    (Classical.choice (occurrence_real_receipt I)) k I.centre I.codeExact
    (by simpa only [Nat.add_comm] using Nat.le_of_lt I.codeFit)
    I.width path born wasBorn rootLive B live edges 0 _

#print axioms actual_format_in_native_or_printed_width
#print axioms actual_compiled_atlas_read_formats
end
end J6R62Leaf
