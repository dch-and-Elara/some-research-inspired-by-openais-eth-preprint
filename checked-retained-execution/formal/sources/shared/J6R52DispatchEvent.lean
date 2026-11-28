import J6R51DispatchResidentTape
import J6R51DispatchLegacy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12500000
set_option maxRecDepth 2800

/-! Materialize the same legal event's receiver-ordered exponent words
and its literal ordinal. The old arbitrary order is read; no accidental
equality between the current cursor and the old catalogue is needed. -/
namespace J6R52Dispatch
open scoped Polynomial Classical
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply J6R51Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite

structure EventBytes (q tc tz tm : ℕ) where
  exponents : List (Word q)
  centre : Word tc
  probe : Word tz
  mode : Word tm
  group : Word 6

def materialize {q tc tz tm : ℕ} (a : ℕ) (source receiver : List (RawMode q))
    (dense : List (Word q)) (file : List (List (Word q)))
    (t : Word tc) (z : Word tz) (g : Word 6) : Meter (Option (EventBytes q tc tz tm)) :=
  let m := emitAndReplay a source receiver dense
  match m.result with
  | none => ⟨none,m.steps+4⟩
  | some words =>
    let o := readPriorOrdinal (tm:=tm) words file
    match o.result with
    | none => ⟨none,m.steps+o.steps+5⟩
    | some b =>
      let t' := J6R27OriginalGate.copyFixed t
      let z' := J6R27OriginalGate.copyFixed z
      let g' := J6R27OriginalGate.copyFixed g
      ⟨some ⟨words,t'.result,z'.result,b,g'.result⟩,
        m.steps+o.steps+t'.steps+z'.steps+g'.steps+8⟩

def replayCap {q : ℕ} (a : ℕ) (src : List (RawMode q)) (dense : List (Word q))
    (targetCount : ℕ) : ℕ :=
  src.length*dispatchStride a q+4+
    (2+targetCount*(3*q+7+(supportSpec src dense).length*(60*a+30*q+35)))+3

def ordinalCap (q tm targetCount fileCount : ℕ) : ℕ :=
  3*tm+7+fileCount*(targetCount*(10*q+9)+13*tm+12)

def metadataFee (tc tz : ℕ) : ℕ := (3*tc+1)+(3*tz+1)+(3*6+1)+8

variable {f : ℤ[X]} {ell s C q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem literal_prior_mode_ordinal (T : Prepared cfg sel root hf) (v : Ticket sel root)
    (I : SiteTape sel (ticketReady T v) v.centerAt q)
    (file : List (List (Word q))) (fileExact : file=frozenCatalogueBytes T v I)
    (query : List (Word q)) (actual : query.map Word.val=vectorKey sel (ticketReady T v) v.centerAt I v.modeAt)
    {tm : ℕ} (ht : 0<tm) (fit : file.length<2^tm) :
    let out := readPriorOrdinal (tm:=tm) query file
    out.result=some (word (modeOrdinal T v)) ∧
      (word (q:=tm) (modeOrdinal T v)).val=modeOrdinal T v ∧
      out.steps≤ordinalCap q tm query.length file.length := by
  let μ := v.modeAt
  let modes := ((ticketActive T v).tape v.centerAt).modes
  let enc := fun β=> (vectorKey sel (ticketReady T v) v.centerAt I β).map (word (q:=q))
  have dense : enc μ=query := by
    change (vectorKey sel (ticketReady T v) v.centerAt I v.modeAt).map (word (q:=q))=query
    rw [←actual,List.map_map]
    exact (List.map_congr_left (fun u (_ : u∈query)=>valued_word u)).trans (List.map_id _)
  have fileSpec : file=modes.map enc := fileExact
  have contains : query∈file := by
    rw [←dense,fileSpec]
    exact List.mem_map_of_mem (f:=enc) (((ticketActive T v).tape v.centerAt).modeComplete μ)
  have idx : file.idxOf query=modeOrdinal T v := by
    rw [←dense,fileSpec]
    refine (idx_of_real_beq_encoding enc (live_event_encoding_injective T v I) μ modes).trans ?_
    unfold modeOrdinal
    apply same_index_for_lawful_comparators <;> infer_instance
  obtain ⟨result,fee⟩ := read_prior_ordinal_correct (tm:=tm) query file ht fit contains
  have room : modeOrdinal T v<2^tm :=
    idx ▸ (List.idxOf_lt_length_iff.mpr contains).trans fit
  rw [idx] at result
  exact ⟨result,word_val room,fee⟩

theorem native_materialized_event (T : Prepared cfg sel root hf) (v : Ticket sel root)
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
    {tc tz tm : ℕ} (t : Word tc) (z : Word tz) (g : Word 6)
    (file : List (List (Word (q+1))))
    (fileExact : file=frozenCatalogueBytes T v (residentLiteralTape (ticketReady T v) v.centerAt H))
    (ht : 0<tm) (fit : file.length<2^tm) :
    let a := (S).levelBits v.parent.depth
    let out := materialize (tm:=tm) a src R.raw.roster.modes dense file t z g
    ∃ E : EventBytes (q+1) tc tz tm, out.result=some E ∧
      E.centre=t ∧ E.probe=z ∧ E.group=g ∧ E.mode.val=modeOrdinal T v ∧
      E.exponents.map Word.val=H.modes.map
        (fun m=>siteTuple sel (ticketReady T v) v.slot.val ((packet_mode_equiv
          (packing sel (ticketReady T v)).mask (centerIndex (ticketReady T v) v.centerAt)
          (registerPrecision S v.parent v.centerAt)).symm m)) ∧
      out.steps≤replayCap a src dense H.modes.length +
        ordinalCap (q+1) tm H.modes.length file.length + metadataFee tc tz := by
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
  obtain ⟨key,keyVal,issueFee⟩ := literal_prior_mode_ordinal T v
    (residentLiteralTape d v.centerAt H) file fileExact ready good ht fit
  rw [width] at issueFee
  unfold materialize
  dsimp only
  rw [reads]
  dsimp only
  rw [key]
  dsimp only
  simp only [J6R27OriginalGate.copy_fixed_exact]
  refine ⟨⟨ready,t,z,word (modeOrdinal T v),g⟩,rfl,rfl,rfl,rfl,keyVal,acts,?_⟩
  change (_+_+(3*tc+1)+(3*tz+1)+(3*6+1)+8)≤_+_+metadataFee tc tz
  unfold metadataFee
  change (emitAndReplay ((S).levelBits v.parent.depth) src R.raw.roster.modes dense).steps ≤
    replayCap ((S).levelBits v.parent.depth) src dense H.modes.length at replayFee
  omega

#print axioms materialize
#print axioms literal_prior_mode_ordinal
#print axioms native_materialized_event
end J6R52Dispatch

