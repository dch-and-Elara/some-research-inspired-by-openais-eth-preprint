import J6R32StatefulArithmeticChronology
import J6R32StatefulArithmeticFolds

/-! Exact writer chronology and non-writer fee through literal ordered
loops. Logs are proof-side recurrences on the same local lists, not a
different program that computes or requests all responses first. -/
namespace J6R32StatefulArithmetic
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6R30ProducedGateRegistry

structure Log (L J : Type*) where
  jobs : List J
  extras : L→ℕ

variable {key prec tw bw : ℕ} {D : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D
local notation "LogL" => Log L J

def Log.empty : LogL := ⟨[],fun _=>0⟩

def Log.append (x y : LogL) : LogL :=
  ⟨x.jobs++y.jobs,fun B=>x.extras B+y.extras (afterJobs B x.jobs)⟩

def Log.enter (x : J) (l : LogL) : LogL :=
  ⟨x::l.jobs,fun B=>l.extras (afterOne B x)+4⟩

def Log.each {A : Type*} (f : A→LogL) : List A→LogL
  | [] => Log.empty
  | a::as => (f a).append (Log.each f as)

theorem log_literal_order {A : Type*} (f : A→LogL) (xs : List A) :
    (Log.each f xs).jobs=xs.flatMap (fun a=>(f a).jobs) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [Log.each,Log.append,List.flatMap_cons,ih]

abbrev Follows {A : Type*} (P : L→Prop) (run : SM L A) (ref : Meter A) (l : LogL) :=
  Traced P run ref l.jobs l.extras

theorem walk_follows {A B : Type*} {P : L→Prop} (stable : StableBank P)
    (nil : Meter B) (op : B→B→Meter B) (read : A→SM L B) (ref : A→Meter B)
    (logs : A→LogL) (xs : List A) (h : ∀ a∈xs,Follows P (read a) (ref a) (logs a)) :
    Follows P (walk nil op read xs) (walkRef nil op ref xs) (Log.each logs xs) := by
  induction xs with
  | nil => exact nil_traced P nil
  | cons a as ih =>
    exact (h a List.mem_cons_self).combine stable
      (ih (fun k hk=>h k (List.mem_cons_of_mem _ hk))) op

variable {p ell : ℕ} {fw : List (Word p)}
variable (hp : 0<p)

theorem sumWords_follows {A : Type*} {P : L→Prop} (stable : StableBank P)
    (rd : A→SM L (UVBlock fw ell)) (ref : A→Meter (UVBlock fw ell))
    (logs : A→LogL) (as : List A) (h : ∀ i∈as,Follows P (rd i) (ref i) (logs i)) :
    Follows P (sumWords hp rd as) (sumM hp ref as) (Log.each logs as) := by
  have e : walkRef (zeroM hp) (addWord hp) ref as=sumM hp ref as := by
    clear h
    induction as with
    | nil => rfl
    | cons i is ih => rw [walkRef,sumM,ih,merge_add]
  rw [←e]
  exact walk_follows stable _ _ _ _ _ _ h

theorem prodWords_follows {A : Type*} {P : L→Prop} (stable : StableBank P)
    (he : 0<fw.length) (hv : 0<ell) (rd : A→SM L (UVBlock fw ell))
    (ref : A→Meter (UVBlock fw ell)) (logs : A→LogL) (as : List A)
    (h : ∀ i∈as,Follows P (rd i) (ref i) (logs i)) :
    Follows P (prodWords hp he hv rd as) (foldM hp he hv ref as) (Log.each logs as) := by
  have e : walkRef (oneM hp he hv) (mulWord hp) ref as=foldM hp he hv ref as := by
    clear h
    induction as with
    | nil => rfl
    | cons i is ih => rw [walkRef,foldM,ih,merge_mul]
  rw [←e]
  exact walk_follows stable _ _ _ _ _ _ h

def groupLog {Mode : Type*} {G : ℕ} (child : Mode→Fin G→LogL) (ms : List Mode) : LogL :=
  Log.each (fun β=>Log.each (child β) (groupOrder G)) ms

theorem grouped_follows {Mode : Type*} {G : ℕ} {P : L→Prop} (stable : StableBank P)
    (he : 0<fw.length) (hv : 0<ell) (ms : List Mode) (child : Mode→Fin G→SM L (UVBlock fw ell))
    (ref : Mode→Fin G→Meter (UVBlock fw ell)) (logs : Mode→Fin G→LogL)
    (exactChild : ∀ m∈ms,∀ g,Follows P (child m g) (ref m g) (logs m g)) :
    Follows P (grouped hp he hv ms child) (groupedProbe hp he hv ms ref) (groupLog logs ms) := by
  apply sumWords_follows hp stable
  intro β hβ
  exact prodWords_follows hp stable he hv (child β) (ref β) (logs β) _ (fun g _=>exactChild β hβ g)

variable {k : ℕ} (he : 0<fw.length)

theorem sumJets_follows {A : Type*} {P : L→Prop} (stable : StableBank P)
    (rd : A→SM L (JetTape fw ell k)) (ref : A→Meter (JetTape fw ell k))
    (logs : A→LogL) (as : List A) (h : ∀ i∈as,Follows P (rd i) (ref i) (logs i)) :
    Follows P (sumJets hp he rd as) (paidJetSum hp he ref as) (Log.each logs as) := by
  have e : walkRef ⟨jetZero hp he k,tapeFee fw.length ell p k⟩ (addJet hp he) ref as=paidJetSum hp he ref as := by
    clear h
    induction as with
    | nil => rfl
    | cons i is ih => simp only [walkRef,paidJetSum,ih,merge2,addJet,padCost,Nat.add_assoc]
  rw [←e]
  exact walk_follows stable _ _ _ _ _ _ h

#print axioms log_literal_order
#print axioms walk_follows
#print axioms sumWords_follows
#print axioms prodWords_follows
#print axioms grouped_follows
#print axioms sumJets_follows
end J6R32StatefulArithmetic
