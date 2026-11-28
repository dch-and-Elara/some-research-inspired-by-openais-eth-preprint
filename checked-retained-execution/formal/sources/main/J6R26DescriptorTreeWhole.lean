import J6R26DescriptorTreeNative
import J6R26DescriptorTreeQueue

/-! Compile/check the true invocation headers before running the very
same prepared recursion. The compiled bank and schedule are shared;
the metered registry stage is not a second arithmetic computation
and the proof-side history list is not charged as execution again. -/
namespace J6R26DescriptorTree
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R16ModeCost

def expectedPayload {w b d p : ℕ} (J : Job w b d p) : List Bool :=
  (J.make (⟨word (q:=1) 0,0⟩ : Meter (Word 1))).result.bytes

theorem Job.bytes_ignore_ordinal {w b d p q : ℕ} (J : Job w b d p) (key : Meter (Word q)) :
    (J.make key).result.bytes=expectedPayload J := rfl

theorem history_payloads {w b d p key : ℕ} (last : Word key) (jobs : List (Job w b d p)) :
    (historyRows last jobs).map DirRow.bytes=jobs.map expectedPayload := by
  induction jobs generalizing last with
  | nil => rfl
  | cons j js ih =>
    simp only [historyRows,List.map_cons,Job.bytes_ignore_ordinal,ih]

def scheduleThenRun {A : Type*} {w b d p key : ℕ} (state : LedgerState key)
    (jobs : List (Job w b d p)) (invoke : Unit→Meter A) : Meter (LedgerState key×Option A) :=
  let made := emitJobs state jobs
  if made.result.2 then
    let read := invoke ()
    ⟨(made.result.1,some read.result),made.steps+read.steps+4⟩
  else ⟨(made.result.1,none),made.steps+4⟩

theorem sequence_success {A : Type*} {w b d p key : ℕ} (state : LedgerState key)
    (jobs : List (Job w b d p)) (invoke : Unit→Meter A)
    (h : (emitJobs state jobs).result.2=true) :
    scheduleThenRun state jobs invoke=
      ⟨((emitJobs state jobs).result.1,some (invoke ()).result),(emitJobs state jobs).steps+(invoke ()).steps+4⟩ := by
  simp only [scheduleThenRun,h,if_true]

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf)

abbrev ByteSupply (w b dep p tc tz tm : ℕ) := ∀ v : Ticket sel r,NativeJob T v w b dep p tc tz tm

variable {w b dep p tc tz tm : ℕ}
variable (L : ByteSupply T w b dep p tc tz tm)

noncomputable def preparedJobs : List (Job w b dep p) :=
  (allTickets T).map (fun v=>(L v).job)

noncomputable def preparedSchedule {key : ℕ} (S : LedgerState key) :
    Meter (LedgerState key×Option (Block (T.frame (.reflexive _)) ell)) :=
  scheduleThenRun S (preparedJobs T L) (fun _=>T.run r (.reflexive _))

theorem prepared_job_count :
    (preparedJobs T L).length+1=
      ∑ j∈Finset.range (pathLimit s C+1),(occurrences (Plan sel) r j).length := by
  rw [preparedJobs,List.length_map,all_tickets_count]

theorem prepared_record_payloads {key : ℕ} (last : Word key) :
    (historyRows last (preparedJobs T L)).map DirRow.bytes=(allTickets T).map (fun v=>
      (L v).coordinates++childHeaderBytes (word (q:=p) v.child.prec)
        (word (q:=dep) v.child.depth) (word (q:=b) v.child.edges)
        ((((L v).physical.physicalSelected v.groupAt).map (L v).physical.record).flatMap rowBytes)) := by
  rw [history_payloads,preparedJobs,List.map_map]
  apply List.map_congr_left
  intro v _
  exact ((L v).literal_bytes (⟨word (q:=1) 0,0⟩ : Meter (Word 1))).2

variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

set_option maxHeartbeats 3000000 in
theorem prepared_schedule_is_priced {key : ℕ} (hk : 0<key) (S : LedgerState key) (good : S.good)
    (fit : S.last.val+(preparedJobs T L).length<2^key) :
    let run := preparedSchedule T L S
    let plain := T.run r (.reflexive _)
    let jobs := preparedJobs T L
    run.result.2=some plain.result ∧
    (T.frame (.reflexive _)).decode plain.result=reduce r.prec f ell (r.host.contract hf) ∧
    run.result.1.bank=(historyRows S.last jobs).reverse++S.bank ∧
    run.result.1.last.val=S.last.val+jobs.length ∧
    (∀ (id : Word key), id.val ≤ S.last.val →(fetch id run.result.1.bank).result=(fetch id S.bank).result) ∧
    run.steps=scheduleFee S.last (fetchFee S.bank) jobs+
      (∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.localAt j)+4 := by
  let Q := preparedJobs T L
  have h := queue_exact hk S Q good fit
  have equal := sequence_success S Q (fun _=>T.run r (.reflexive _)) h.ok
  have value := relative_prepared_contraction T
  dsimp only [preparedSchedule]
  rw [equal]
  exact ⟨rfl,value.1,h.rows,h.counter,h.old,by rw [h.paid,value.2]⟩

#print axioms history_payloads
#print axioms prepared_job_count
#print axioms prepared_record_payloads
#print axioms prepared_schedule_is_priced
end J6R26DescriptorTree

