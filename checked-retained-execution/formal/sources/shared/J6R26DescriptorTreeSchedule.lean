import J6R26DescriptorTreeRegistry

/-! A concrete chronological header writer. Only the fixed-width ripple
counter provides a new key. Distinct occurrences of equal physical
calls can therefore both have their own fresh row. Active install
and lookup fees come solely from the source bit routines. -/
namespace J6R26DescriptorTree
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply

structure Job (port bits depth prec : ℕ) where
  coordinates : List Bool
  group : Word 6
  precision : Word prec
  parentDepth : Word depth
  ports : List (PortRow port)

structure LedgerState (keyWidth : ℕ) where
  last : Word keyWidth
  bank : List (DirRow keyWidth)

def LedgerState.good {key : ℕ} (s : LedgerState key) : Prop :=
  ∀ row∈s.bank,row.id.val≤s.last.val

def Job.make {w b d p key : ℕ} (J : Job w b d p) (issued : Meter (Word key)) : Meter (DirRow key) :=
  let h := childStage (b:=b) issued J.group J.precision J.parentDepth J.ports
  let bytes := copyBytes (J.coordinates++h.result.bytes)
  ⟨⟨h.result.id,bytes.result⟩,h.steps+bytes.steps+3*J.coordinates.length+5⟩

theorem Job.make_id {w b d p key : ℕ} (J : Job w b d p) (counter : Meter (Word key)) :
    (J.make counter).result.id=counter.result :=
  (child_stage_exact (b:=b) counter J.group J.precision J.parentDepth J.ports).1

theorem Job.make_bytes {w b d p key : ℕ} (J : Job w b d p) (counter : Meter (Word key)) :
    (J.make counter).result.bytes=
      J.coordinates++(childStage (b:=b) counter J.group J.precision J.parentDepth J.ports).result.bytes := by
  unfold Job.make
  dsimp only
  rw [copyBytes_exact]

def stepJob {w b d p key : ℕ} (state : LedgerState key) (J : Job w b d p) :
    Meter (LedgerState key×Bool) :=
  let n := increment state.last
  let h := J.make n
  let out := checkedInstall h state.bank
  ⟨(⟨n.result,out.result.1⟩,out.result.2.isSome),out.steps+key+4⟩

theorem step_job_exact {w b d p key : ℕ} (hk : 0<key) (state : LedgerState key)
    (J : Job w b d p) (good : state.good) (fit : state.last.val+1<2^key) :
    let n := increment state.last
    let h := J.make n
    let R : LedgerState key := ⟨n.result,h.result::state.bank⟩
    stepJob state J=⟨(R,true),installFee h state.bank+key+4⟩ ∧
      R.last.val=state.last.val+1 ∧ h.result.id=R.last ∧ R.good ∧
      ∀ id, (id.val≤state.last.val) → (fetch id R.bank).result=(fetch id state.bank).result := by
  let n := increment state.last
  let h := J.make n
  let R : LedgerState key := ⟨n.result,h.result::state.bank⟩
  have hn : n.result.val=state.last.val+1 := (increment_exact hk state.last fit).1
  have hKey : h.result.id=n.result := J.make_id n
  have fresh (row : DirRow key) (mem : row∈state.bank) : row.id≠h.result.id := by
    intro e
    have p := good row mem
    rw [e,hKey,hn] at p
    omega
  have spec := fresh_install_exact h state.bank fresh
  refine ⟨?_,hn,hKey,?_,?_⟩
  · unfold stepJob
    dsimp only
    rw [show checkedInstall (J.make (increment state.last)) state.bank=_ from spec]
    rfl
  · intro r hr
    rcases List.mem_cons.mp hr with e|e
    · rw [e,hKey]
    · change r.id.val≤n.result.val
      rw [hn]
      exact (good r e).trans (Nat.le_succ _)
  · intro id hId
    have e : h.result.id≠id := by
      intro eq
      have g := congrArg Word.val eq
      rw [hKey,hn] at g
      omega
    exact preserved_read h.result id state.bank e

/-- The one priced actual queue consumer. It requires no preannounced
number of calls at execution; the count is only a capacity hypothesis
of its correctness result. The boolean does not return stale matches. -/
def emitJobs {w b d p key : ℕ} (s : LedgerState key) :
    List (Job w b d p)→Meter (LedgerState key×Bool)
  | [] => ⟨(s,true),2⟩
  | j::js =>
    let first := stepJob s j
    let tail := emitJobs first.result.1 js
    ⟨(tail.result.1,first.result.2 && tail.result.2),first.steps+tail.steps+3⟩

def historyRows {w b d p key : ℕ} (last : Word key) :
    List (Job w b d p)→List (DirRow key)
  | [] => []
  | j::js =>
    let next := increment last
    (j.make next).result::historyRows next.result js

def scheduleFee {w b d p key : ℕ} (last : Word key) (scan : ℕ) :
    List (Job w b d p)→ℕ
  | [] => 2
  | j::js =>
    let next := increment last
    let e := j.make next
    let own := rowFee e.result
    (e.steps+scan+3*e.result.bytes.length+2*key+9+own+4+key+4)+
      scheduleFee next.result (own+scan) js+3

theorem old_row_fetchFee {w : ℕ} (pref bank : List (DirRow w)) :
    fetchFee (pref++bank)=fetchFee bank+(pref.map rowFee).sum := by
  induction pref with
  | nil => simp only [List.nil_append,List.map_nil,List.sum_nil,Nat.add_zero]
  | cons x xs ih =>
    simp only [List.cons_append,fetchFee,List.map_cons,List.sum_cons,ih]
    omega

#print axioms step_job_exact
#print axioms old_row_fetchFee
end J6R26DescriptorTree


