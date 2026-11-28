import J6R48DFSAtlas
import J6R33GeneratedChildSitePublish

/-! Connect the real emitted per-page atlas, including empty pages, to
the scoped stack accounting. This is a receipt for the same mounted
record, not a per-frame array with a free assumed length. -/
namespace J6R48DFS
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6ActiveRun J6R10Reachable J6R9Recursive
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R26DescriptorTree J6R32ChildResidentTransfer J6R33GeneratedChildSite P11FullPacking

set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 2400

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep prec tc tz tm q tw bw code key : ℕ}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "aAt" => J6ActiveRun.Shape.levelBits SP ticket.parent.depth
local notation "iAt" => centerIndex (ticketReady T ticket) ticket.centerAt
local notation "pAt" => registerPrecision SP ticket.parent ticket.centerAt
local notation "hp" => register_positive (ticketReady T ticket) ticket.centerAt
local notation "node" => sampleNode SP f ell ticket.parent (Ready.fit (ticketReady T ticket)) ticket.centerAt ticket.probeAt
local notation "beta" => activeMode sel (ticketReady T ticket) ticket.centerAt ticket.modeAt
variable {fw : List (A1R10.Word (registerPrecision
    (printedParams (f:=f) (ell:=ell) s) ticket.parent ticket.centerAt))}
variable {R : ChildResidents ((printedParams (f:=f) (ell:=ell) s).levelBits ticket.parent.depth) q}
variable {H : ResidentReceipt (packing sel (ticketReady T ticket))
    (centerIndex (ticketReady T ticket) ticket.centerAt)
    (registerPrecision (printedParams (f:=f) (ell:=ell) s) ticket.parent ticket.centerAt) R}

theorem issued_atlas_counts_real_pages
    (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key))
    (X : ActiveWords fw (q+1) tw bw) (hOld : 0<fw.length)
    {hv : 0<ell} {fit : (iAt).val+1≤q+1}
    {hMod : A1R10.Modulus pAt hp fw=NativeProbeRing.liftPoly pAt f}
    (A : AtlasReceipt (code:=code) H X hp hv fit hMod node ticket.groupAt beta) :
    (issuedBirth J issued X hOld A).job.immutable.payload.payload.pages.length=
      Nat.card ticket.child.host.Col := by
  let d := ticketReady T ticket
  let b := siteTuple sel d ticket.slot.val
  have a := congrArg (fun x : Call (PhysicalHost f ell) => x.host.Col) (child_exact sel d ticket.slot.val)
  have E : ticket.child.host.Col =
      Page (aAt) (packing sel d).copies (Fin 64) :=
    a.trans (packet_columns_are_pages d ticket.centerAt ticket.probeAt b ticket.groupAt)
  change A.bank.length=Nat.card ticket.child.host.Col
  rw [A.order,List.length_map,E,ordered_child_page_count]

#print axioms issued_atlas_counts_real_pages
end J6R48DFS
