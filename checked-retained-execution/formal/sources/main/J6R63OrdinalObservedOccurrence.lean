import J6R63OrdinalObservedRun

/-! The observed probe belongs to the active branch of the same ranked
scoped runner, with its mounted resident and actual recursive child.
No alternate runner, re-acquisition, or outer bootstrap is observed. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost J6R25PreparedSupply
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
open J6R51ParentFrames J6R51Online J6R52CacheWhole J6R54PeakInput J6R58OrdinalSpace
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4500
set_option maxHeartbeats 13200000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable {B : Base T key prec tw bw page (q+1)}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
variable (D : Program B b) (retire : PageJob f ell key prec tw bw page→ℕ)
variable (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
variable (X : StoredSite T (p.ticket u) key prec tw bw page)
variable (resident : ResidentBank X) (bank : PageBank f ell key prec tw bw page)

def actualRankedReadAt (on : (SP).cutoff<((P).child c u).edges) :
    ActiveReader (B.activeAfter p u X on).result (centreArchiveOrdinal T (Path.step p u) on) b := by
  let current := (P).child c u
  let path := Path.step p u
  let d := ready_reachable cfg sel path.reached T.rootStable on
  let cache := (mountResident X resident).result
  intro t z β raw i exactRaw exactRank g
  let w := addressed (sel:=sel) d t z β g
  let request := D.prepare p u X cache on t z β g raw
  have trueRank := exactRank.trans (centre_archive_word_is_original_ticket_ordinal T path on t z β g)
  let obtained := acceptCurrent request raw i exactRaw trueRank
  exact project (openBankDemandSingleEmission obtained cache retire
    (fun next held=>runFrom D retire current path w next held)
    (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) bank)

theorem active_ranked_runner_uses_this_actual_probe_reader
    (on : (SP).cutoff<((P).child c u).edges) :
    let mounted := mountResident X resident
    let A := B.activeAfter p u X on
    let phase := rankedActive A.result (centreArchiveOrdinal T (Path.step p u) on)
      B.modeWidth D.ordinalWidth (reachable_positive T (Path.step p u).reached)
      T.vPositive hf (D.archive p u X on) (actualRankedReadAt D retire c p u X resident bank on)
    runFrom D retire c p u X resident bank=
      ⟨(phase.result,bank),mounted.steps+A.steps+phase.steps⟩ := by
  dsimp only
  have nocut : ¬((P).child c u).edges≤(SP).cutoff := not_le.mpr on
  rw [runFrom,rankedDescendantStep,dif_neg nocut]; rfl

variable {c p u X}
variable (on : (printedParams (f:=f) (ell:=ell) s).cutoff<((@Plan f ell s sel).child c u).edges)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) ((@Plan f ell s sel).child c u))
variable (z : Probe (printedParams (f:=f) (ell:=ell) s) ((@Plan f ell s sel).child c u))
local notation "Ctr" => (((B.activeAfter p u X on).result.tape t))
local notation "I" => ((((B.activeAfter p u X on).result.tape t).tape.result))
local notation "O" => (centreArchiveOrdinal T (Path.step p u) on t)

theorem actual_descendant_probe_has_the_selected_ordinal_words
    {seed here : Pending (q+1) (I).words.length} {ordinal : Word b}
    (began : (startingCursor I B.modeWidth).result=some seed)
    (progress : ClockPrefix seed here ordinal)
    {raw : List (Word (q+1))} {st : State (q+1)} (emit : here.pulse.result=.emit raw st) :
    ∃ (bits : List Bool) (live : SuffixFits I O here ordinal) (value : Block (Ctr).low ell) (paid : ℕ),
      let read := actualRankedReadAt D retire c p u X resident bank on t z
      let drain := checkedDrain _ _ (native_paid_emit_law I O D.ordinalWidth)
        (updateRanked (Ctr).low I O T.vPositive read) here ordinal live value paid
      ordinalObservedWords here ordinal=some bits ∧ bits.length=(I).words.length*(q+1)+2*b ∧
        runProbeRanked (Ctr).low I O B.modeWidth D.ordinalWidth T.vPositive (D.archive p u X on t) read=
          ⟨drain.result.1,drain.steps⟩ := by
  have words := real_ranked_site_observes_one_row_and_two_ordinal_words I O B.modeWidth
    D.ordinalWidth (D.archive p u X on t) began progress emit
  dsimp only at words
  obtain ⟨live,v,fee,same⟩ := ranked_probe_reaches_its_actual_suffix_meter (Ctr).low I O
    B.modeWidth D.ordinalWidth T.vPositive (D.archive p u X on t)
    (actualRankedReadAt D retire c p u X resident bank on t z) began progress
  exact ⟨_,live,v,fee,words.1,words.2,same⟩

#print axioms actualRankedReadAt
#print axioms active_ranked_runner_uses_this_actual_probe_reader
#print axioms actual_descendant_probe_has_the_selected_ordinal_words
end
end J6R63Ordinal
