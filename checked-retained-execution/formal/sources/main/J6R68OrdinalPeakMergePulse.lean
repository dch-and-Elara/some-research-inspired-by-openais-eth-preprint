import J6R68OrdinalPeakMergeReader
import J6R63OrdinalObservedWords

/-! Follow the ranked cursor of the actual live R66 centre: a chosen
row is licensed only after its literal start and paid event prefix.
The reported children use this same group product, not an address
selected from a separate, already computed run. -/
namespace J6R68.OrdinalPeakMerge
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost J6R25PreparedSupply
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R21Ancestor J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R48RawRoute J6R49DFS
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52Dispatch J6R52CacheWhole
open J6R62ActivePrep J6R58OrdinalSpace J6R63Ordinal J6R63Active J6R64Active J6R66Active
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4600
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 15000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {M : OnlineMachine T key prec tw bw page (q+1)}
variable {F : RetainedAfter T key prec tw bw page (q+1) cw}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "E" => (Entered T key prec tw bw page)

abbrev atTape (M : OnlineMachine T key prec tw bw page (q+1))
    (F : RetainedAfter T key prec tw bw page (q+1) cw) (x : E)
    (on : (SP).cutoff<x.call.edges) (t : Center SP x.call) :=
  ((atActive M F x on).result.tape t).tape.result

structure PulseWitness (R : RankedRequests M F b) (x : E)
    (on : (SP).cutoff<x.call.edges) (t : Center SP x.call) where
  first : Pending (q+1) (atTape M F x on t).words.length
  now : Pending (q+1) (atTape M F x on t).words.length
  index : Word b
  raw : List (Word (q+1))
  following : State (q+1)
  starts : (startingCursor (atTape M F x on t) M.modeWidth).result=some first
  history : ClockPrefix first now index
  fires : now.pulse.result=.emit raw following

variable {R : RankedRequests M F b} {x : Entered T key prec tw bw page}
variable {on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) x.call}
variable (P : PulseWitness R x on t)
local notation "I" => (atTape M F x on t)
local notation "Ordinal" => (centreArchiveOrdinal T (nowPath x) on t)
local notation "CF" => ((atActive M F x on).result.tape t).low

theorem PulseWitness.legal : LegalRaw I Ordinal P.raw P.index := by
  have ok := genuine_ranked_prefix_invariant I Ordinal M.modeWidth R.positive
    (R.archive x on t) P.starts P.history
  exact ((native_paid_emit_law I Ordinal R.positive).next
    P.now P.index P.raw P.following P.fires ok).1

def PulseWitness.mode : NativeMenu (N sel) x.call t :=
  selectedMode I Ordinal P.raw P.index P.legal

theorem PulseWitness.data :
    P.raw.map Word.val=vectorKey sel (readyAtPath T (nowPath x) on) t I P.mode ∧
      P.index.val=Ordinal P.mode :=
  actual_ordinal_at_decoding I Ordinal P.legal (literal_selected_mode I Ordinal P.raw P.index P.legal)

def PulseWitness.payload : List Bool :=
  (P.raw.flatMap Word.bits)++P.index.bits++(increment P.index).result.bits

theorem real_pulse_observation_is_same_row_and_two_words :
    ordinalObservedWords P.now P.index=some P.payload ∧
      P.payload.length=(I).words.length*(q+1)+2*b :=
  real_ranked_site_observes_one_row_and_two_ordinal_words I Ordinal M.modeWidth R.positive
    (R.archive x on t) P.starts P.history P.fires

def actualGroupLoad (cache : CachedParentFrames x.site.site) (z : Probe SP x.call) (g : Fin 64) :
    Meter (LocalLoad x.site (atAddress x on t z P.mode g)) :=
  rankedLoad R x cache on t z P.mode P.raw P.index P.data.1 P.data.2 g

def actualGroupCallback (cache : CachedParentFrames x.site.site) (retire : J → ℕ) (recur : StateContinuation x)
    (z : Probe SP x.call) (g : Fin 64) : Meter (Block CF ell) :=
  rankedHeaderReader R retire x cache on recur t z P.mode P.raw P.index P.data.1 P.data.2 g

theorem actual_ranked_pulse_uses_these_same_64_group_calls
    (cache : CachedParentFrames x.site.site) (retire : J → ℕ) (recur : StateContinuation x) (z : Probe SP x.call) (acc : Block CF ell) :
    updateRanked CF I Ordinal T.vPositive (rankedHeaderReader R retire x cache on recur t z)
      acc P.raw P.index P.legal=
      addM (CF).hp ⟨acc,0⟩ (product64 (CF).hp (CF).sizePos T.vPositive (actualGroupCallback P cache retire recur z)) :=
  rfl

theorem the_actual_live_header_probe_is_at_this_prefix
    (cache : CachedParentFrames x.site.site) (retire : J → ℕ) (recur : StateContinuation x) (z : Probe SP x.call) :
    ∃ (fit : SuffixFits I Ordinal P.now P.index) (val : Block CF ell) (fee : ℕ),
      let read := rankedHeaderReader R retire x cache on recur t z
      let tail := checkedDrain _ _ (native_paid_emit_law I Ordinal R.positive)
        (updateRanked CF I Ordinal T.vPositive read) P.now P.index fit val fee
      runProbeRanked CF I Ordinal M.modeWidth R.positive T.vPositive (R.archive x on t) read=
        ⟨tail.result.1,tail.steps⟩ :=
  ranked_probe_reaches_its_actual_suffix_meter CF I Ordinal M.modeWidth R.positive T.vPositive
    (R.archive x on t) (rankedHeaderReader R retire x cache on recur t z) P.starts P.history

#print axioms PulseWitness
#print axioms PulseWitness.data
#print axioms real_pulse_observation_is_same_row_and_two_words
#print axioms actual_ranked_pulse_uses_these_same_64_group_calls
#print axioms the_actual_live_header_probe_is_at_this_prefix
end
end J6R68.OrdinalPeakMerge

