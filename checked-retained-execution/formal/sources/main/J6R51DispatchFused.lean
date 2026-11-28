import J6R51DispatchLegacy
import J6R51DispatchResidentTape

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 2700

/-! Sequential execution of the paid physical reindexing and the old
address issuer. The initial complete old catalogue is explicitly kept
as an input, priced per read below, rather than fabricated by Lean. -/
namespace J6R51Dispatch
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite

def emitReplayAndIssue {q tc tz tm : ℕ} (a : ℕ) (source receiver : List (RawMode q))
    (dense : List (Word q)) (file : List (List (Word q)))
    (t : Word tc) (z : Word tz) (g : Word 6) :
    Meter (Option (Word (tc+(tz+(tm+6))))) :=
  let m := emitAndReplay a source receiver dense
  match m.result with
  | none => ⟨none,m.steps+4⟩
  | some query =>
    let out := lookupAndIssue (tm:=tm) query file t z g
    ⟨out.result,m.steps+out.steps+4⟩

variable {f : ℤ[X]} {ell s C q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem actual_emission_to_legacy_address (T : Prepared cfg sel root hf)
    (v : Ticket sel root)
    (I : SiteTape sel (ticketReady T v) v.centerAt (q+1))
    {R : ChildResidents ((S).levelBits v.parent.depth) q}
    (H : ResidentReceipt (packing sel (ticketReady T v)) (centerIndex (ticketReady T v) v.centerAt)
          (registerPrecision S v.parent v.centerAt) R)
    (src : List (RawMode (q+1)))
    (srcExact : src=I.modes.map (encodeMode (centerIndex (ticketReady T v) v.centerAt)))
    (dense : List (Word (q+1)))
    (actual : dense.map Word.val=vectorKey sel (ticketReady T v) v.centerAt I v.modeAt)
    (pageRoom : (packing sel (ticketReady T v)).copies<2^(q+1))
    (tileRoom : 2^((centerIndex (ticketReady T v) v.centerAt).val+1)<2^(q+1))
    {port edge dep prec tc tz tm : ℕ} (D : NativeJob T v port edge dep prec tc tz tm)
    (file : List (List (Word (q+1))))
    (fileExact : file=frozenCatalogueBytes T v (residentLiteralTape (ticketReady T v) v.centerAt H))
    (ht : 0<tm) (fit : file.length<2^tm) :
    let a := (S).levelBits v.parent.depth
    let out := emitReplayAndIssue (tm:=tm) a src R.raw.roster.modes dense file D.tWord D.zWord D.gWord
    let replayCap := src.length*dispatchStride a (q+1)+4+
      (2+H.modes.length*(3*(q+1)+7+(supportSpec src dense).length*(60*a+30*(q+1)+35)))+3
    let issueCap := 3*tm+7+file.length*(H.modes.length*(10*(q+1)+9)+13*tm+12)+
      (6*(tc+(tz+(tm+6)))+10)+4
    (out.result.map Word.bits)=some D.coordinates ∧ out.steps≤replayCap+issueCap+4 := by
  let d := ticketReady T v
  let w : NativeAddress (shape S (sourceDelta s) sel) v.parent := v.slot.val
  obtain ⟨ready,reads,acts,replayFee⟩ :=
    actual_resident_exponents_replayed d w I H src srcExact dense actual pageRoom tileRoom
  have good : ready.map Word.val=vectorKey sel d v.centerAt (residentLiteralTape d v.centerAt H) v.modeAt :=
    acts.trans (resident_acted_exactly_destination_vector d w H)
  have width : ready.length=H.modes.length := by
    have h := congrArg List.length acts
    rw [List.length_map,List.length_map] at h
    exact h
  obtain ⟨key,issueFee⟩ := read_actual_frozen_order_and_issue T v
    (residentLiteralTape d v.centerAt H) D file fileExact ready good ht fit
  rw [width] at issueFee
  unfold emitReplayAndIssue
  dsimp only
  rw [reads]
  dsimp only
  exact ⟨key,Nat.add_le_add_right (Nat.add_le_add replayFee issueFee) _⟩

#print axioms emitReplayAndIssue
#print axioms actual_emission_to_legacy_address
end J6R51Dispatch

