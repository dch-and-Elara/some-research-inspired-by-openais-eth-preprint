import J6R52DispatchEvent
import J6R27OriginalGateModeCompare

/-! One emitted coordinate vector is replayed into the true receiver
order. An already certified ordinal word is copied, not recovered by
scanning a materialized table. Correct ordinal provenance is separate. -/
namespace J6R58OrdinalSpace
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R27OriginalGate
open J6R51Dispatch J6R52Dispatch
set_option autoImplicit false
set_option maxHeartbeats 10000000

def materializeWithRank {q tc tz tm : ℕ} (a : ℕ) (source receiver : List (RawMode q))
    (emit : List (Word q)) (t : Word tc) (z : Word tz) (g : Word 6) (ord : Word tm) :
    Meter (Option (EventBytes q tc tz tm)) :=
  let m := emitAndReplay a source receiver emit
  match m.result with
  | none => ⟨none,m.steps+4⟩
  | some words =>
    let t' := copyFixed t
    let z' := copyFixed z
    let g' := copyFixed g
    let rank := copyFixed ord
    ⟨some ⟨words,t'.result,z'.result,rank.result,g'.result⟩,
      m.steps+t'.steps+z'.steps+g'.steps+8+rank.steps⟩

theorem ordinal_event_word_and_charge_at_actual_receiver {q tc tz tm : ℕ}
    (a : ℕ) (source receiver : List (RawMode q)) (raw ready : List (Word q))
    (t : Word tc) (z : Word tz) (g : Word 6) (ord : Word tm)
    (checked : (emitAndReplay a source receiver raw).result=some ready) :
    materializeWithRank a source receiver raw t z g ord=
      ⟨some ⟨ready,t,z,ord,g⟩,(emitAndReplay a source receiver raw).steps+metadataFee tc tz+(3*tm+1)⟩ := by
  unfold materializeWithRank
  dsimp only
  rw [checked]
  dsimp only
  simp only [copy_fixed_exact,metadataFee]
  congr 1
  omega

theorem live_rank_replaces_the_legacy_search_at_the_same_result {q tc tz tm : ℕ}
    (a : ℕ) (source receiver : List (RawMode q)) (raw ready : List (Word q))
    (file : List (List (Word q))) (t : Word tc) (z : Word tz) (g : Word 6) (ord : Word tm)
    (checked : (emitAndReplay a source receiver raw).result=some ready)
    (same : (readPriorOrdinal (tm:=tm) ready file).result=some ord) :
    let next := materializeWithRank a source receiver raw t z g ord
    let old := materialize (tm:=tm) a source receiver raw file t z g
    next.result=old.result ∧
      next.steps+(readPriorOrdinal (tm:=tm) ready file).steps=old.steps+(3*tm+1) := by
  dsimp only
  rw [ordinal_event_word_and_charge_at_actual_receiver a source receiver raw ready t z g ord checked]
  unfold materialize
  dsimp only
  rw [checked]
  dsimp only
  rw [same]
  dsimp only
  simp only [copy_fixed_exact,metadataFee]
  exact ⟨True.intro,by omega⟩

#print axioms ordinal_event_word_and_charge_at_actual_receiver
#print axioms live_rank_replaces_the_legacy_search_at_the_same_result
end J6R58OrdinalSpace
