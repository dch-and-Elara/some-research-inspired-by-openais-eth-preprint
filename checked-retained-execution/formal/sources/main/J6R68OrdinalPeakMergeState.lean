import J6R68OrdinalPeakMergeReader

/-! Replacement at the exact R66 state-body boundary. The physical
preparer, current live header, parent cache, leaf and continuation
are unchanged. The reference comparison is only of returned values;
the ordinal and acquisition tariffs are allowed to change. -/
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
set_option maxRecDepth 4550
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 16700000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {M : OnlineMachine T key prec tw bw page (q+1)}
variable {F : RetainedAfter T key prec tw bw page (q+1) cw}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "E" => (Entered T key prec tw bw page)

def stateBodyWithCurrentRank (R : RankedRequests M F b) (retire : J → ℕ)
    (x : E) (recur : StateContinuation x) : EntryOut x :=
  if stop : x.call.edges≤(SP).cutoff then
    let value := M.leafAfter x.path x.slot x.site stop x.bank
    ⟨(value.result,x.bank),value.steps⟩
  else
    let on := Nat.lt_of_not_ge stop
    let A := atActive M F x on
    let mounted := mountResident x.site x.resident
    let out := rankedActive A.result (centreArchiveOrdinal T (nowPath x) on)
      M.modeWidth R.positive (reachable_positive T (nowPath x).reached) T.vPositive hf
      (R.archive x on) (rankedHeaderReader R retire x mounted.result on recur)
    ⟨(out.result,x.bank),mounted.steps+A.steps+out.steps⟩

def HasOldCheckedWiring (R : RankedRequests M F b) : Prop :=
  ∀ (x : E) (cache : CachedParentFrames x.site.site) (on : (SP).cutoff<x.call.edges) (t : Center SP x.call)
    (z : Probe SP x.call) (β : NativeMenu (N sel) x.call t) (g : Fin 64)
    (raw : List (Word (q+1))),
    let Q := R.current x cache on t z β g raw
    raw.map Word.val=vectorKey sel (readyAtPath T (nowPath x) on) t
      ((atActive M F x on).result.tape t).tape.result β →
    ∃ old : Meter (Option (EventBytes (q+1) Q.result.tc Q.result.tz b)),
      ∃ checked : CheckedEvent Q.result.replay old,
        (M.demand x.site (atAddress x on t z β g)).result=
          (acceptLocalLoad Q.result.replay Q.result.shell Q.result.directory old checked).result

theorem live_rank_load_and_old_scope_use_same_packet_and_return
    (R : RankedRequests M F b) (wired : HasOldCheckedWiring R)
    (retire : J → ℕ) (x : E) (cache : CachedParentFrames x.site.site) (on : (SP).cutoff<x.call.edges) (recur : StateContinuation x)
    (t : Center SP x.call) (z : Probe SP x.call) (β : NativeMenu (N sel) x.call t)
    (raw : List (Word (q+1))) (i : Word b)
    (goodRaw : raw.map Word.val=vectorKey sel (readyAtPath T (nowPath x) on) t
      ((atActive M F x on).result.tape t).tape.result β)
    (goodRank : i.val=centreArchiveOrdinal T (nowPath x) on t β) (g : Fin 64) :
    let now := rankedLoad R x cache on t z β raw i goodRaw goodRank g
    let old := M.demand x.site (atAddress x on t z β g)
    let newRead := rankedHeaderReader R retire x cache on recur t z β raw i goodRaw goodRank g
    let oldRead := oldHeaderReader (M:=M) retire x cache on recur t z β g
    now.result=old.result ∧ newRead.result=oldRead.result ∧
      newRead.steps+old.steps=oldRead.steps+now.steps := by
  let req := R.current x cache on t z β g raw
  have correct := goodRank.trans (centre_archive_word_is_original_ticket_ordinal T (nowPath x) on t z β g)
  obtain ⟨before,accepted,uses⟩ := wired x cache on t z β g raw goodRaw
  have loads : (rankedLoad R x cache on t z β raw i goodRaw goodRank g).result=
      (M.demand x.site (atAddress x on t z β g)).result :=
    (current_request_preserves_the_legacy_local_result req goodRaw correct before accepted).trans uses.symm
  refine ⟨loads,?_⟩
  let w := atAddress x on t z β g
  let d := readyAtPath T (nowPath x) on
  let go : (next : StoredSite T (successorTicket (x.path.ticket x.slot) w) key prec tw bw page) →
      WithIncoming next (Block (T.bank (registerPrecision SP x.call t) (register_positive d t)) ell) :=
    fun n reg bank owned=>recur ⟨x.call,nowPath x,w,n,reg,bank,owned⟩ ((@Plan f ell s sel).smaller x.call w)
  let fail : Meter (Block (T.bank (registerPrecision SP x.call t) (register_positive d t)) ell) :=
    zeroM (T.bank (registerPrecision SP x.call t) (register_positive d t)).hp
  have same := scope_changes_only_its_acquisition_when_data_agree
    (rankedLoad R x cache on t z β raw i goodRaw goodRank g) (M.demand x.site w)
    cache retire go fail x.bank loads
  exact ⟨congrArg Prod.fst same.2.1,same.2.2⟩

theorem one_r66_state_can_switch_its_active_reader_without_changing_value
    (R : RankedRequests M F b) (wired : HasOldCheckedWiring R)
    (retire : J → ℕ) (x : E) (recur : StateContinuation x) :
    (stateBodyWithCurrentRank R retire x recur).result=(stateBody M F retire x recur).result := by
  by_cases stop : x.call.edges≤(SP).cutoff
  · rw [stateBodyWithCurrentRank,stateBody,dif_pos stop,dif_pos stop]
  · let on := Nat.lt_of_not_ge stop
    let A := atActive M F x on
    let ord := centreArchiveOrdinal T (nowPath x) on
    let cache := (mountResident x.site x.resident).result
    let actual := rankedHeaderReader R retire x cache on recur
    let old := oldHeaderReader (M:=M) retire x cache on recur
    have word : (rankedActive A.result ord M.modeWidth R.positive
        (reachable_positive T (nowPath x).reached) T.vPositive hf (R.archive x on) actual).result=
        (A.result.eval M.modeWidth (reachable_positive T (nowPath x).reached) T.vPositive hf old).result := by
      apply ranked_active_keeps_actual_decoded_word
      intro t z β raw i bits idx g
      exact (live_rank_load_and_old_scope_use_same_packet_and_return R wired retire x cache on recur
        t z β raw i bits idx g).2.1
    rw [stateBodyWithCurrentRank,stateBody,dif_neg stop,dif_neg stop]
    exact congrArg (fun word=>(word,x.bank)) word

#print axioms stateBodyWithCurrentRank
#print axioms HasOldCheckedWiring
#print axioms live_rank_load_and_old_scope_use_same_packet_and_return
#print axioms one_r66_state_can_switch_its_active_reader_without_changing_value
end
end J6R68.OrdinalPeakMerge

