import J6R52DispatchEvent
import J6R49DFSVisitMath

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 2750

/-! The directly executable raw pulse+materializer, independent of the
recursive consumer. The output contains values, not only joined bits:
the receiving exponent vector and each of four address fields. -/
namespace J6R52Dispatch
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply J6R51Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite A1R12 J6R22Active J6R48DFS J6R49DFS

def pulseMaterialBytes {q len tc tz tm : ℕ} (pending : Pending q len)
    (a : ℕ) (source receiver : List (RawMode q))
    (file : List (List (Word q))) (t : Word tc) (z : Word tz) (g : Word 6) :
    Meter (Option (EventBytes q tc tz tm)) :=
  let pulse := pending.pulse
  match pulse.result with
  | .again _ => ⟨none,pulse.steps+4⟩
  | .halt => ⟨none,pulse.steps+4⟩
  | .emit words _ =>
    let out := materialize (tm:=tm) a source receiver words file t z g
    ⟨out.result,pulse.steps+out.steps+4⟩

variable {f : ℤ[X]} {ell s C q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem actual_probe_material_bytes (T : Prepared cfg sel root hf)
    (v : Ticket sel root)
    (I : SiteTape sel (ticketReady T v) v.centerAt (q+1))
    (F : Frame f (registerPrecision S v.parent v.centerAt))
    (live : 0<ell)
    (child : NativeMenu (shape S (sourceDelta s) sel) v.parent v.centerAt → Fin 64 → Meter (Block F ell))
    (begin : Pending (q+1) I.words.length)
    (begun : (startingCursor I (Nat.zero_lt_succ q)).result=some begin)
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
    {tc tz tm : ℕ} (ct : Word tc) (zz : Word tz) (gg : Word 6)
    (file : List (List (Word (q+1))))
    (fileExact : file=frozenCatalogueBytes T v (residentLiteralTape (ticketReady T v) v.centerAt H))
    (ht : 0<tm) (fit : file.length<2^tm) :
    let a := (S).levelBits v.parent.depth
    let out := pulseMaterialBytes (tm:=tm) now a src R.raw.roster.modes file ct zz gg
    ∃ E : EventBytes (q+1) tc tz tm, out.result=some E ∧
      E.centre=ct ∧ E.probe=zz ∧ E.group=gg ∧ E.mode.val=modeOrdinal T v ∧
      E.exponents.map Word.val=H.modes.map
        (fun m=>siteTuple sel (ticketReady T v) v.slot.val ((packet_mode_equiv
          (packing sel (ticketReady T v)).mask (centerIndex (ticketReady T v) v.centerAt)
          (registerPrecision S v.parent v.centerAt)).symm m)) ∧
      out.steps≤now.pulse.steps+(replayCap a src raw H.modes.length+
        ordinalCap (q+1) tm H.modes.length file.length+metadataFee tc tz)+4 := by
  obtain ⟨β,rβ,vector⟩ :=
    legal_emission_from_real_probe F I (Nat.zero_lt_succ q) live child begin begun now outer fee previous raw next emit
  have same : β=v.modeAt := Option.some.inj (rβ.symm.trans addressed)
  subst β
  obtain ⟨E,bytes,tExact,zExact,gExact,mExact,acted,cost⟩ :=
    native_materialized_event T v I H src srcExact raw vector.symm pageRoom tileRoom
      (tm:=tm) ct zz gg file fileExact ht fit
  unfold pulseMaterialBytes
  dsimp only
  rw [emit]
  dsimp only
  exact ⟨E,bytes,tExact,zExact,gExact,mExact,acted,Nat.add_le_add_right (Nat.add_le_add_left cost _) _⟩

#print axioms pulseMaterialBytes
#print axioms actual_probe_material_bytes
end J6R52Dispatch

