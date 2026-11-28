import J6R63OrdinalWhole
import J6R63OrdinalDispatchLaws
import J6R63OrdinalScope

/-! All-depth comparison with the existing source interpreter.
The comparison premise concerns the OLD request's attachment to the
same shell, directory and checked event. The new request is generated
from the running cursor; equality of child results is proved, not
assumed. Old and new fees need not be equal. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
open J6R51ParentFrames J6R51Online J6R52CacheWhole J6R54PeakInput J6R52Dispatch J6R25PreparedSupply
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 5400
set_option maxHeartbeats 36500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Here" => (Path.root : Path sel r r)
variable (M : OnlineMachine T key prec tw bw page (q+1))
variable (D : Program (Base.ofOnline M) b)

def LegacyWiring : Prop :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (cache : CachedParentFrames X.site)
    (on : (SP).cutoff<((P).child c u).edges) (t : Center SP ((P).child c u))
    (z : Probe SP ((P).child c u)) (β : NativeMenu (N sel) ((P).child c u) t) (g : Fin 64)
    (raw : List (Word (q+1))),
    let d := ready_reachable cfg sel (Path.step p u).reached T.rootStable on
    let w := addressed (sel:=sel) d t z β g
    let A := (D.prepare p u X cache on t z β g raw).result
    raw.map Word.val=vectorKey sel d t ((M.activeAfter p u X on).result.tape t).tape.result β →
    ∃ measure : Meter (Option (EventBytes (q+1) A.tc A.tz b)), ∃ good : CheckedEvent A.replay measure,
      (M.demand X w).result=(acceptLocalLoad A.replay A.shell A.directory measure good).result

variable (wired : LegacyWiring M D)
include wired

theorem all_ranked_descendant_values_are_the_original_values (retire : J→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (live : ResidentBank X) (bank : L) :
    (runFrom D retire c p u X live bank).result.1=
      (runCachedAfterSingleEmission M retire c p u X live bank).result.1 := by
  let current := (P).child c u
  let path := Path.step p u
  by_cases stop : current.edges≤(SP).cutoff
  · rw [runFrom,rankedDescendantStep,dif_pos stop,runCachedAfterSingleEmission,dif_pos stop]; rfl
  · let on := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel path.reached T.rootStable on
    let A := (M.activeAfter p u X on).result
    let cache := (mountResident X live).result
    let ord := centreArchiveOrdinal T path on
    let go : ActiveReader A ord b := fun t z β raw i rawExact rankExact g=>
      let w := addressed (sel:=sel) d t z β g
      let trueRank := rankExact.trans (centre_archive_word_is_original_ticket_ordinal T path on t z β g)
      let currentRequest := D.prepare p u X cache on t z β g raw
      let obtained := acceptCurrent currentRequest raw i rawExact trueRank
      project (openBankDemandSingleEmission obtained cache retire
        (fun next held=>runFrom D retire current path w next held)
        (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) bank)
    let ref : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openBankDemandSingleEmission (M.demand X w) cache retire
        (fun next held=>runCachedAfterSingleEmission M retire current path w next held)
        (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) bank)
    have matched : ∀ (t : Center SP current) (z : Probe SP current)
        (β : NativeMenu (N sel) current t) (raw : List (J6R15ModeCost.Word (q+1)))
        (i : J6R15ModeCost.Word b)
        (rawExact : raw.map Word.val=vectorKey sel d t (A.tape t).tape.result β)
        (clock : i.val=ord t β) (g : Fin 64), (go t z β raw i rawExact clock g).result=(ref t z β g).result := by
      intro t z β raw i rawExact clock g
      let w := addressed (sel:=sel) d t z β g
      let fixed := clock.trans (centre_archive_word_is_original_ticket_ordinal T path on t z β g)
      let req := D.prepare p u X cache on t z β g raw
      let load := acceptCurrent req raw i rawExact fixed
      obtain ⟨oldEvent,good,previous⟩ := wired p u X cache on t z β g raw rawExact
      have source : load.result=(M.demand X w).result :=
        (current_request_preserves_the_legacy_local_result req rawExact fixed oldEvent good).trans previous.symm
      let bad : Meter (Block (T.bank (registerPrecision SP current t) (register_positive d t)) ell) :=
        zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp
      let nextNew := fun next held=>runFrom D retire current path w next held
      let nextRef := fun next held=>runCachedAfterSingleEmission M retire current path w next held
      change (openBankDemandSingleEmission load cache retire nextNew bad bank).result.1=
        (openBankDemandSingleEmission (M.demand X w) cache retire nextRef bad bank).result.1
      apply congrArg Prod.fst
      apply singular_scope_keeps_same_result_with_current_load _ _ _ _ _ _ _ _ source
      intro next held bank'
      exact all_ranked_descendant_values_are_the_original_values retire current path w next held bank'
    rw [runFrom,rankedDescendantStep,dif_neg stop,runCachedAfterSingleEmission,dif_neg stop]
    change (rankedActive A ord M.modeWidth D.ordinalWidth (reachable_positive T path.reached)
      T.vPositive hf (D.archive p u X on) go).result=
      (A.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf ref).result
    exact ranked_active_keeps_actual_decoded_word A ord M.modeWidth D.ordinalWidth
      (reachable_positive T path.reached) T.vPositive hf (D.archive p u X on) go ref matched
termination_by ((@Plan f ell s sel).child c u).edges
decreasing_by exact (@Plan f ell s sel).smaller _ _

theorem whole_ranked_runner_same_original_output (retire : J→ℕ) (bank : L) :
    (runRoot D retire bank).result=(runCachedRootSingleEmission M retire bank).result := by
  by_cases stop : r.edges≤(SP).cutoff
  · rw [runRoot,dif_pos stop,runCachedRootSingleEmission,dif_pos stop]; rfl
  · let on := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel (Here).reached T.rootStable on
    let A := (M.activeRoot on).result
    let owned : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (bootBankDemand (M.initial w) retire (runFrom D retire r Here w)
        (zeroM (T.bank (registerPrecision SP r t) (register_positive d t)).hp) bank)
    have phase : (A.eval M.modeWidth (reachable_positive T (Here).reached) T.vPositive hf owned).result=
        (A.eval M.modeWidth (reachable_positive T (Here).reached) T.vPositive hf
          (rootReadSingleEmission M retire bank on)).result := by
      apply streaming_value_congr
      intro t z β g
      let w := addressed (sel:=sel) d t z β g
      let bad : Meter (Block (T.bank (registerPrecision SP r t) (register_positive d t)) ell) :=
        zeroM (T.bank (registerPrecision SP r t) (register_positive d t)).hp
      change (bootBankDemand (M.initial w) retire (runFrom D retire r Here w) bad bank).result.1=
        (bootBankDemand (M.initial w) retire (runCachedAfterSingleEmission M retire r Here w) bad bank).result.1
      apply congrArg Prod.fst
      exact same_first_scope_uses_ranked_continuation _ _ _ _ _ _
        (fun next held bank'=>all_ranked_descendant_values_are_the_original_values M D wired retire
          r Here w next held bank')
    rw [runRoot,dif_neg stop,runCachedRootSingleEmission,dif_neg stop]
    exact congrArg (fun word=>(word,bank)) phase

theorem whole_ranked_runner_keeps_the_original_cached_result (retire : J→ℕ) (bank : L) :
    (runRoot D retire bank).result=(runCachedRoot M retire bank).result :=
  (whole_ranked_runner_same_original_output M D wired retire bank).trans
    (congrArg Meter.result
      (the_entire_root_run_has_the_same_meter_with_single_deep_emission M retire bank))

#print axioms all_ranked_descendant_values_are_the_original_values
#print axioms whole_ranked_runner_same_original_output
#print axioms whole_ranked_runner_keeps_the_original_cached_result
end
end J6R63Ordinal
