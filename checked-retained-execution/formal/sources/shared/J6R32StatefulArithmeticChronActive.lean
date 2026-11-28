import J6R32StatefulArithmeticActive
import J6R32StatefulArithmeticChronFold

/-! This is the exact accounting of the same local runtime. At each
stage the next writer or reader sees the state actually returned by the
preceding stage. In particular the ghost chronology does not pre-run
all child installations. -/
namespace J6R32StatefulArithmetic
open AOracleMachineTime A1R10 A1R12 J6R22Active J6R30ProducedGateRegistry

set_option maxHeartbeats 4500000

section Local
variable {key prec tw bw : ℕ} {D : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D
local notation "LogL" => Log L J

variable {p ell n k : ℕ} {fw : List (Word p)}
variable (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)
variable {P : Ledger key prec tw bw D→Prop}

theorem term_follows (stable : StableBank P) (node : Fin n→Meter (UVBlock fw ell))
    (sample : Fin n→SM L (UVBlock fw ell)) (ref : Fin n→Meter (UVBlock fw ell))
    (i : Fin n) (l : LogL) (sub : Follows P (sample i) (ref i) l) :
    Follows P (termS hp he hv hk node sample i) (interpTerm hp he hv hk node ref i) l := by
  have H := (nil_traced P (basisM hp he hv hk node i)).combine stable sub
    (fun b y=>padCost (jetMult hp he (jetConst hp he hk y) b) (tapeFee fw.length ell p k+4))
  simpa only [termS,merge2,padCost,interpTerm,Nat.add_assoc,List.nil_append,afterJobs,Nat.zero_add] using H

theorem prefix_follows (stable : StableBank P) (node : Fin n→Meter (UVBlock fw ell))
    (sample : Fin n→SM L (UVBlock fw ell)) (ref : Fin n→Meter (UVBlock fw ell))
    (logs : Fin n→LogL) (sub : ∀ i,Follows P (sample i) (ref i) (logs i)) :
    Follows P (prefixS hp he hv hk node sample) (interpPrefix hp he hv hk node ref)
      (Log.each logs (probeOrder n)) := by
  have H := sumJets_follows hp he stable (termS hp he hv hk node sample)
    (interpTerm hp he hv hk node ref) logs (probeOrder n) (fun z _=>term_follows hp he hv hk stable node sample ref z _ (sub z))
  have Q := H.finish (padWord (4*(n+1)^2+4))
  simpa only [prefixS,merge_pad,padCost,interpPrefix,Nat.add_assoc] using Q

theorem full_follows (stable : StableBank P) (node : Fin n→Meter (UVBlock fw ell))
    (sample : Fin n→SM L (UVBlock fw ell)) (ref : Fin n→Meter (UVBlock fw ell))
    (normal : Meter (JetTape fw ell k)) (logs : Fin n→LogL)
    (sub : ∀ i,Follows P (sample i) (ref i) (logs i)) :
    Follows P (fullS hp he hv hk node sample normal) (fullCenterM hp he hv hk node ref normal)
      (Log.each logs (probeOrder n)) := by
  have h := (nil_traced P normal).combine stable (prefix_follows hp he hv hk stable node sample ref logs sub)
    (fun E j=>padCost (divideJet hp he hv hk E j) 4)
  simpa only [fullS,merge2,padCost,fullCenterM,Nat.add_assoc,List.nil_append,afterJobs,Nat.zero_add] using h

def siteLog {M : Type*} (modes : List M) (logs : Fin n→M→Fin 64→LogL) : LogL :=
  Log.each (fun z=>groupLog (logs z) modes) (probeOrder n)

theorem site_follows {M : Type*} (stable : StableBank P) (J0 : SiteTape p ell k n M) (a : ℕ) (t : ℤ)
    (child : Fin n→M→Fin 64→SM L (UVBlock J0.fw ell)) (logs : Fin n→M→Fin 64→LogL)
    (sub : ∀ z m g,Follows P (child z m g) (J0.child z m g) (logs z m g)) :
    Follows P (siteS J0 a t child) (J0.run a t) (siteLog J0.modes logs) :=
  full_follows J0.hp J0.nonempty J0.he J0.hk stable J0.nodeM _ _ (J0.normM a t) _
    (fun z=>grouped_follows J0.hp stable J0.nonempty J0.he J0.modes (child z) (J0.child z) (logs z)
      (fun m _ g=>sub z m g))
end Local

section Active
open scoped Polynomial
open Polynomial J6R19Retained J6R23ScheduleWeight J6R24MeteredRecursion
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted

variable {key prec tw bw : ℕ} {D : Type*}
local notation "L" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D
local notation "LogL" => Log L J
variable {f : ℤ[X]} {ell s : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f} {P : Ledger key prec tw bw D→Prop}
local notation "a" => (Shape.levelBits S (Call.depth c))
local notation "u" => (Shape.levelWidth S (Call.depth c))

abbrev ChildLog (ρ K : Type*) (t : Center S c) :=
  Probe S c→NativeMenu (N sel) c t→Fin 64→Log ρ K

abbrev ActiveLog (ρ K : Type*) :=
  ∀ t : Center S c,ChildLog (sel:=sel) ρ K t

def callLog (A : ActiveDesc sel d bank) (logs : ActiveLog (sel:=sel) (c:=c) L J) : LogL :=
  Log.each (fun t=>siteLog (A.tape t).modes (logs t)) A.centres

variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
local notation "pₜ" => (registerPrecision S c t)
local notation "kₜ" => (order (Call.edges c) u (Subtype.val t))

set_option maxHeartbeats 2500000 in
theorem centre_follows {q : ℕ} (stable : StableBank P) (A : CentreDesc sel d t bank)
    (hv : 0<ell) (hf : f.Monic) (high : Frame f q) (B : ℕ)
    (child : CentreChildS (sel:=sel) L bank d t)
    (ref : CentreChild (sel:=sel) (d:=d) (t:=t) bank) (logs : ChildLog (sel:=sel) L J t)
    (sub : ∀ z m g,Follows P (child z m g) (ref z m g) (logs z m g)) :
    Follows P (centreS A hv hf high B child) (A.centre hv hf high B ref) (siteLog A.modes logs) := by
  let F := bank pₜ (register_positive d t)
  have h := site_follows stable (A.site hv ref) a t.val child logs sub
  have z := h.finish (fun jet=>
    padCost (sumM high.hp (A.term hv hf high B jet) (List.range kₜ)) (tapeFee F.words.length ell pₜ kₜ+4))
  simpa only [merge,padCost,CentreDesc.centre,Nat.add_assoc] using z

set_option maxHeartbeats 3200000 in
theorem active_follows (stable : StableBank P) (A : ActiveDesc sel d bank) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChildS (sel:=sel) L bank d) (ref : ActiveChild (sel:=sel) (d:=d) bank)
    (logs : ActiveLog (sel:=sel) (c:=c) L J)
    (sub : ∀ t z m g,Follows P (child t z m g) (ref t z m g) (logs t z m g)) :
    Follows P (activeS A hp hv hf child) (A.eval hp hv hf ref) (callLog A logs) := by
  have x : Follows P (highS A hp hv hf child) (A.highRun hp hv hf ref) (callLog A logs) :=
    sumWords_follows (A.high hp).hp stable _ _ _ _ (fun t _=>
      centre_follows stable (A.tape t) hv hf (A.high hp) A.extraPrecision (child t) (ref t) (logs t) (sub t))
  have y := x.finish (fun v=>
    padCost (stripUVLoop (((A.high hp).natDegree hf).trans ((bank c.prec hp).natDegree hf).symm) v) 4)
  have z : Follows P (finishS A hp hv hf child) (A.finish hp hv hf ref) (callLog A logs) := by
    simpa only [finishS,merge,ActiveDesc.finish,padCost,Nat.add_assoc] using y
  exact traced_check z

#print axioms term_follows
#print axioms prefix_follows
#print axioms full_follows
#print axioms site_follows
#print axioms centre_follows
#print axioms active_follows
end Active
end J6R32StatefulArithmetic
