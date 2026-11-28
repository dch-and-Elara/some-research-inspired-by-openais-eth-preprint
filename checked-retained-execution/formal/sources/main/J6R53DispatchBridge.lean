import J6R52DispatchAccept
import J6R52DispatchPulseMaterial
import J6R51DispatchResidentWidths

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 17000000
set_option maxRecDepth 3450
set_option linter.unusedSectionVars false

/-! Integration of the actual reachable R49 pulse and the true R51
LocalLoad sidecar transaction. The complete old catalogue remains a
physically explicit file; the tactic does not create it. -/
namespace J6R53Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply J6R51Dispatch J6R52Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion J6R34ChildPath J6R41StructuredAllPaths
open J6R32ChildResidentTransfer J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open A1R12 J6R22Active J6R48DFS J6R49DFS J6R50SourceProducer J6R51Online
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q} (R : Replayed X.site w q U)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "nx" => (J6R48RawRoute.successorTicket v w)
local notation "d" => (ticketReady T (J6R48RawRoute.successorTicket v w))
local notation "t" => (Ticket.centerAt (J6R48RawRoute.successorTicket v w))
local notation "A" => ((S).levelBits v.child.depth)
local notation "p" => (registerPrecision S v.child t)

theorem actual_pulse_checks_loaded_ticket
    (I : SiteTape sel d t (q+1)) (F : Frame f p) (live : 0<ell)
    (child : NativeMenu (shape S (sourceDelta s) sel) v.child t → Fin 64 → Meter (Block F ell))
    (begin : Pending (q+1) I.words.length)
    (begun : (startingCursor I (Nat.zero_lt_succ q)).result=some begin)
    (now : Pending (q+1) I.words.length) (outer : Block F ell) (fee : ℕ)
    (previous : ModePrefix (modeUpdate F I live child) begin
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I (Nat.zero_lt_succ q)).steps)
      now outer fee)
    (raw : List (Word (q+1))) (next : State (q+1)) (emit : now.pulse.result=.emit raw next)
    (addressed : decodeAt I raw=some (nx).modeAt)
    (src : List (RawMode (q+1))) (srcExact : src=I.modes.map (encodeMode (centerIndex d t)))
    {tc tz tm : ℕ} (ct : Word tc) (zz : Word tz) (gg : Word 6)
    (ctExact : ct.val=centerOrdinal T nx) (zzExact : zz.val=(nx).probeAt.val)
    (ggExact : gg.val=(nx).groupAt.val)
    (file : List (List (Word (q+1))))
    (fileExact : file=frozenCatalogueBytes T nx (residentLiteralTape d t R.certificate))
    (ht : 0<tm) (fit : file.length<2^tm) :
    let out := pulseMaterialBytes (tm:=tm) now A src R.resident.raw.roster.modes file ct zz gg
    CheckedEvent R out ∧
      out.steps≤now.pulse.steps+(replayCap A src raw R.certificate.modes.length+
        ordinalCap (q+1) tm R.certificate.modes.length file.length+metadataFee tc tz)+4 := by
  obtain ⟨page,tiles⟩ := resident_dispatch_fields_fit (centerIndex d t) R.certificate U.widthFit
  obtain ⟨E,bytes,tExact,zExact,gExact,mExact,acted,cost⟩ :=
    actual_probe_material_bytes T nx I F live child begin begun now outer fee previous raw next emit addressed
      R.certificate src srcExact page tiles (tm:=tm) ct zz gg file fileExact ht fit
  exact ⟨⟨E,bytes,⟨tExact.symm ▸ ctExact,zExact.symm ▸ zzExact,mExact,gExact.symm ▸ ggExact,acted⟩⟩,cost⟩

#print axioms actual_pulse_checks_loaded_ticket
end
end J6R53Dispatch

