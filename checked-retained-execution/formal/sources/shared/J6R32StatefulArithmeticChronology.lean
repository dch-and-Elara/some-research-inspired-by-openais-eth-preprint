import J6R32StatefulArithmeticCore
import J6R30ProducedGateRegistryPackedUse
import J6R30ProducedGateRegistryDFS

/-! A chronological ledger is a proof of the live state transaction,
not a job list that the evaluator executes before arithmetic. The ghost
list is used only to state exact costs of the executed publications. -/
namespace J6R32StatefulArithmetic
open AOracleMachineTime A1R12
open J6R30ProducedGateRegistry

variable {key prec tw bw : ℕ} {D : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D

def StableBank (P : L→Prop) : Prop :=
  ∀ B js,JobsReady B js→P B→P (afterJobs B js)

structure TracedAt {A : Type*} (B : L) (js : List J) (out : Meter (A×L))
    (ref : Meter A) (extra : ℕ) : Prop where
  value : out.result.1=ref.result
  state : out.result.2=afterJobs B js
  fee : out.steps=ref.steps+chronologicalBill B js+extra

def Traced {A : Type*} (P : L→Prop) (run : SM L A) (ref : Meter A)
    (js : List J) (extra : L→ℕ) : Prop :=
  ∀ B,JobsReady B js→P B→TracedAt B js (run B) ref (extra B)

theorem nil_traced {A : Type*} (P : L→Prop) (ref : Meter A) :
    Traced P (stationary ref) ref [] (fun _=>0) := by
  intro B _ _
  exact ⟨rfl,rfl,by simp [stationary,chronologicalBill]⟩

theorem Traced.finish {A B : Type*} {P : L→Prop} {x : SM L A}
    {r : Meter A} {js : List J} {d : L→ℕ} (h : Traced P x r js d) (f : A→Meter B) :
    Traced P (finish x f) (merge r f) js d := by
  intro B hz hp
  obtain ⟨v,q,w⟩ := h B hz hp
  refine ⟨?_,q,?_⟩
  · change (f (x B).result.1).result=(f r.result).result
    rw [v]
  · change (x B).steps+(f (x B).result.1).steps=r.steps+(f r.result).steps+chronologicalBill B js+d B
    rw [v,w]
    omega

theorem Traced.combine {A B C : Type*} {P : L→Prop} {x : SM L A} {y : SM L B}
    {r : Meter A} {t : Meter B} {js ks : List J} {d e : L→ℕ} (stable : StableBank P)
    (h : Traced P x r js d) (w : Traced P y t ks e) (f : A→B→Meter C) :
    Traced P (combine x y f) (merge2 r t f) (js++ks)
      (fun bank=>d bank+e (afterJobs bank js)) := by
  intro bank hz hP
  obtain ⟨h1,h2⟩ := jobs_split_ready bank js ks hz
  obtain ⟨c,s,rFee⟩ := h bank h1 hP
  have hp' := stable bank js h1 hP
  obtain ⟨a,b,tFee⟩ := w (afterJobs bank js) h2 hp'
  refine ⟨?_,?_,?_⟩
  · change (f (x bank).result.1 (y (x bank).result.2).result.1).result=(f r.result t.result).result
    rw [c,s,a]
  · change (y (x bank).result.2).result.2=afterJobs bank (js++ks)
    rw [s,b,after_jobs_concatenate]
  · change (x bank).steps+(y (x bank).result.2).steps+
      (f (x bank).result.1 (y (x bank).result.2).result.1).steps=
        r.steps+t.steps+(f r.result t.result).steps+chronologicalBill bank (js++ks)+_
    rw [c,s,a,rFee,tFee,chronological_split]
    dsimp only
    omega

/-- This is run at the precise child invocation point of the arithmetic
interpreter. No child arithmetic runs if publication fails. There is no
directory rollback and no result oracle. -/
def withPublished {A : Type*} (j : J) (go : SM L A) (bad : Meter A) : SM L A := fun bank=>
  let installed := j.install bank
  if installed.result.2 then
    let out := go installed.result.1
    ⟨out.result,installed.steps+out.steps+4⟩
  else ⟨(bad.result,installed.result.1),installed.steps+bad.steps+4⟩

theorem enter_traced {A : Type*} {P Q : L→Prop} (j : J) (go : SM L A) (bad ref : Meter A)
    (js : List J) (d : L→ℕ) (cross : ∀ B,JobsReady B (j::js)→P B→Q (afterOne B j))
    (h : Traced Q go ref js d) :
    Traced P (withPublished j go bad) ref (j::js) (fun B=>d (afterOne B j)+4) := by
  intro B hr hP
  obtain ⟨native,rest⟩ := next_job_exact B j js hr
  obtain ⟨v,hS,fee⟩ := h (afterOne B j) rest (cross B hr hP)
  rw [withPublished,native]
  dsimp only
  simp only [if_true]
  refine ⟨v,hS,?_⟩
  change publishFee B j.entry j.offset j.built+(go (afterOne B j)).steps+4=
    ref.steps+(publishFee B j.entry j.offset j.built+chronologicalBill (afterOne B j) js)+_
  rw [fee]
  omega

theorem traced_check {A : Type*} {P : L→Prop} {bad : Meter A}
    {x : SM L (Option A)} {r : Meter (Option A)} {js : List J} {d : L→ℕ}
    (h : Traced P x r js d) :
    Traced P (stripCheck bad x) (J6R24MeteredRecursion.checkedWord bad r) js d := by
  have q := h.finish (fun a=>match a with | some v=>⟨v,2⟩ | none=>⟨bad.result,bad.steps+2⟩)
  convert q using 1
  cases hr:r.result <;> simp [merge,J6R24MeteredRecursion.checkedWord,hr,Nat.add_assoc]

#print axioms Traced.finish
#print axioms Traced.combine
#print axioms enter_traced
#print axioms traced_check
end J6R32StatefulArithmetic
