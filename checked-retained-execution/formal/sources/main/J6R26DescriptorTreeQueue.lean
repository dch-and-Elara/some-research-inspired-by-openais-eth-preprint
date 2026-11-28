import J6R26DescriptorTreeSchedule

/-! Exact chronological fee and immutable read view over the whole
stream. The result records the physically constructed bank but does
not additionally materialize a second list of historical descriptors
at runtime. The history list is only a proof-side specification. -/
namespace J6R26DescriptorTree
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply

def successive (start : ℕ) : ℕ→List ℕ
  | 0 => []
  | n+1 => start::successive (start+1) n

theorem history_ids {w b d p key : ℕ} (hw : 0<key) (last : Word key)
    (jobs : List (Job w b d p)) (fit : last.val+jobs.length<2^key) :
    (historyRows last jobs).map (fun e=>e.id.val)=successive (last.val+1) jobs.length := by
  induction jobs generalizing last with
  | nil => rfl
  | cons j js ih =>
    let n := increment last
    have hFit : last.val+1<2^key := by simp only [List.length_cons] at fit; omega
    have hN : n.result.val=last.val+1 := (increment_exact hw last hFit).1
    have hTail : n.result.val+js.length<2^key := by
      rw [hN]
      simp only [List.length_cons] at fit
      omega
    have hHead : (j.make n).result.id=n.result :=
      j.make_id n
    rw [historyRows,List.map_cons,show (j.make (increment last)).result.id=n.result from hHead,
      List.length_cons,successive]
    change n.result.val::(historyRows n.result js).map (fun e=>e.id.val)=_
    rw [ih n.result hTail,hN]

structure QueueExact {w b d p key : ℕ} (initial : LedgerState key)
    (jobs : List (Job w b d p)) : Prop where
  ok : (emitJobs initial jobs).result.2=true
  counter : (emitJobs initial jobs).result.1.last.val=initial.last.val+jobs.length
  rows : (emitJobs initial jobs).result.1.bank=(historyRows initial.last jobs).reverse++initial.bank
  invariants : (emitJobs initial jobs).result.1.good
  paid : (emitJobs initial jobs).steps=scheduleFee initial.last (fetchFee initial.bank) jobs
  old : ∀ (id : Word key), id.val ≤ initial.last.val →
    (fetch id (emitJobs initial jobs).result.1.bank).result=(fetch id initial.bank).result

set_option maxHeartbeats 2200000 in
theorem queue_exact {w b d p key : ℕ} (hw : 0<key) (initial : LedgerState key)
    (jobs : List (Job w b d p)) (good : initial.good) (fit : initial.last.val+jobs.length<2^key) :
    QueueExact initial jobs := by
  induction jobs generalizing initial with
  | nil => exact ⟨rfl,by simp only [emitJobs,List.length_nil,Nat.add_zero],rfl,good,rfl,fun _ _=>rfl⟩
  | cons j js ih =>
    let n := increment initial.last
    let e := j.make n
    let next : LedgerState key := ⟨n.result,e.result::initial.bank⟩
    have hfit : initial.last.val+1<2^key := by simp only [List.length_cons] at fit; omega
    obtain ⟨eq,hn,_,ngood,old⟩ := step_job_exact hw initial j good hfit
    have hfit2 : next.last.val+js.length<2^key := by
      change n.result.val+js.length<2^key
      rw [show n.result.val=initial.last.val+1 from hn]
      simp only [List.length_cons] at fit
      omega
    let T := emitJobs next js
    have h := ih next ngood hfit2
    have all : emitJobs initial (j::js)=
        ⟨(T.result.1,T.result.2),installFee e initial.bank+key+4+T.steps+3⟩ := by
      rw [emitJobs,eq]
      rfl
    constructor
    · rw [all]
      exact h.ok
    · rw [all]
      change T.result.1.last.val=initial.last.val+(j::js).length
      rw [h.counter,List.length_cons]
      change n.result.val+js.length=_
      rw [show n.result.val=initial.last.val+1 from hn]
      omega
    · rw [all]
      change T.result.1.bank=_
      rw [h.rows]
      change (historyRows n.result js).reverse++e.result::initial.bank=_
      simp only [historyRows,List.reverse_cons,List.append_assoc,List.singleton_append,e,n]
    · rw [all]
      exact h.invariants
    · rw [all]
      change _+T.steps+3=_
      rw [h.paid]
      change _+scheduleFee n.result (fetchFee (e.result::initial.bank)) js+3=_
      simp only [fetchFee,scheduleFee,installFee,e,n]
    · intro id hOld
      rw [all]
      change (fetch id T.result.1.bank).result=_
      exact (h.old id (hOld.trans (by rw [show next.last.val=initial.last.val+1 from hn]; omega))).trans
        (old id hOld)

def emptyStore (w : ℕ) : LedgerState w := ⟨word 0,[]⟩

theorem start_empty_queue {w b d p key : ℕ} (hk : 0<key)
    (jobs : List (Job w b d p)) (fit : jobs.length<2^key) :
    QueueExact (emptyStore key) jobs := by
  apply queue_exact hk _ jobs (by intro r h; cases h)
  change (word (q:=key) 0).val+jobs.length<2^key
  rw [word_val (by positivity : 0<2^key),Nat.zero_add]
  exact fit

#print axioms history_ids
#print axioms queue_exact
#print axioms start_empty_queue
end J6R26DescriptorTree



