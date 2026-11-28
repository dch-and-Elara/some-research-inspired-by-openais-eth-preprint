import J6R51DispatchFused
import J6R49DFSVisitMath

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 16000000
set_option maxRecDepth 2900

/-! Transfer of the live pulse itself. Its result and charge are both
read by the address assembler; the semantic selected ticket is a proof
of what that pulse denotes, not a runtime decoding primitive. -/
namespace J6R51Dispatch
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite
open A1R12 J6R22Active J6R48DFS J6R49DFS

def livePulseIssue {q len tc tz tm : ℕ} (pending : Pending q len)
    (a : ℕ) (source receiver : List (RawMode q))
    (file : List (List (Word q))) (t : Word tc) (z : Word tz) (g : Word 6) :
    Meter (Option (Word (tc+(tz+(tm+6))))) :=
  let pulse := pending.pulse
  match pulse.result with
  | .again _ => ⟨none,pulse.steps+4⟩
  | .halt => ⟨none,pulse.steps+4⟩
  | .emit words _ =>
    let out := emitReplayAndIssue (tm:=tm) a source receiver words file t z g
    ⟨out.result,pulse.steps+out.steps+4⟩

variable {f : ℤ[X]} {ell s C q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem actual_probe_pulse_issues_legacy_address (T : Prepared cfg sel root hf)
    (v : Ticket sel root)
    (I : SiteTape sel (ticketReady T v) v.centerAt (q+1))
    (F : Frame f (registerPrecision S v.parent v.centerAt))
    (live : 0<ell)
    (child : NativeMenu (shape S (sourceDelta s) sel) v.parent v.centerAt → Fin 64 → Meter (Block F ell))
    (begin : Pending (q+1) I.words.length)
    (begun : (startingCursor I (Nat.zero_lt_succ q)).result = some begin)
    (now : Pending (q+1) I.words.length) (outer : Block F ell) (fee : ℕ)
    (previous : ModePrefix (modeUpdate F I live child) begin
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I (Nat.zero_lt_succ q)).steps)
      now outer fee)
    (raw : List (Word (q+1))) (next : State (q+1)) (emit : now.pulse.result=.emit raw next)
    (addressed : decodeAt I raw=some v.modeAt)
    {R : ChildResidents ((S).levelBits v.parent.depth) q}
    (H : ResidentReceipt (packing sel (ticketReady T v)) (centerIndex (ticketReady T v) v.centerAt)
          (registerPrecision S v.parent v.centerAt) R)
    (src : List (RawMode (q+1)))
    (srcExact : src=I.modes.map (encodeMode (centerIndex (ticketReady T v) v.centerAt)))
    (pageRoom : (packing sel (ticketReady T v)).copies<2^(q+1))
    (tileRoom : 2^((centerIndex (ticketReady T v) v.centerAt).val+1)<2^(q+1))
    {port edge dep prec tc tz tm : ℕ} (D : NativeJob T v port edge dep prec tc tz tm)
    (file : List (List (Word (q+1))))
    (fileExact : file=frozenCatalogueBytes T v (residentLiteralTape (ticketReady T v) v.centerAt H))
    (ht : 0<tm) (fit : file.length<2^tm) :
    let a := (S).levelBits v.parent.depth
    let out := livePulseIssue (tm:=tm) now a src R.raw.roster.modes file D.tWord D.zWord D.gWord
    let replayCap := src.length*dispatchStride a (q+1)+4+
      (2+H.modes.length*(3*(q+1)+7+(supportSpec src raw).length*(60*a+30*(q+1)+35)))+3
    let issueCap := 3*tm+7+file.length*(H.modes.length*(10*(q+1)+9)+13*tm+12)+
      (6*(tc+(tz+(tm+6)))+10)+4
    (out.result.map Word.bits)=some D.coordinates ∧
      out.steps≤now.pulse.steps+(replayCap+issueCap+4)+4 := by
  obtain ⟨β,rβ,exactVector⟩ :=
    legal_emission_from_real_probe F I (Nat.zero_lt_succ q) live child begin begun now outer fee previous raw next emit
  have same : β=v.modeAt := Option.some.inj (rβ.symm.trans addressed)
  subst β
  obtain ⟨result,cost⟩ :=
    actual_emission_to_legacy_address T v I H src srcExact raw exactVector.symm pageRoom tileRoom D file fileExact ht fit
  unfold livePulseIssue
  dsimp only
  rw [emit]
  dsimp only
  exact ⟨result,Nat.add_le_add_right (Nat.add_le_add_left cost _) _⟩

#print axioms livePulseIssue
#print axioms actual_probe_pulse_issues_legacy_address
end J6R51Dispatch

