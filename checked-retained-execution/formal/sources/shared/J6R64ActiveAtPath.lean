import J6R64ActiveMachine
import J6R52CacheWholeRun

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 21000000
set_option maxRecDepth 3800
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! The actual R52 cached continuation with its first requested
active input produced from the live current header. Only active
preparation is substituted; existing paid boot, demand, sidecar,
leaf and retirement logic remain in the same recursion. -/
namespace J6R64Active
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6R63Active J6R62ActivePrep
open J6R51Online J6R51ParentFrames J6R52CacheWhole J6R48RawRoute
open J6ActiveSchedule J6R9Recursive J6R16ModeCost J6R21Ancestor J6R48DFS
open J6R10Repack J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R26DescriptorTree J6R24MeteredRecursion J6R49DFS
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "Here" => (Path.root : Path sel r r)

structure AfterInputs (T : Prepared cfg sel r hf) (key prec tw bw page q cw : ℕ) where
  fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges),
    InputFits sel (readyAtPath T p a) q
  layout : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x)
      (X : StoredSite T (p.ticket w) key prec tw bw page) (B : PageBank f ell key prec tw bw page)
      (_ : OwnsHeader X.birth.job.entry.result B)
      (a : (S).cutoff<((P).child x w).edges),
    Meter (AtLayout sel (readyAtPath T (.step p w) a) cw)

def preparedAfter (M : Machine) (F : AfterInputs T key prec tw bw page q cw)
    (p : Path sel r c) (w : (P).Slot c)
    (X : StoredSite T (p.ticket w) key prec tw bw page) (B : L)
    (own : OwnsHeader X.birth.job.entry.result B)
    (a : (S).cutoff<((P).child c w).edges) :
    Meter (ActiveMachine sel (readyAtPath T (.step p w) a) T.bank q) :=
  let taper := actual_path_taper T (.step p w) a
  sharedMachine M.modeWidth (F.fit (.step p w) a) taper.1 taper.2
    (readIncoming X B own) (F.layout p w X B own a) (M.activeAfter p w X a)

theorem physical_after_setup_charge (M : Machine) (F : AfterInputs T key prec tw bw page q cw)
    (p : Path sel r c) (w : (P).Slot c)
    (X : StoredSite T (p.ticket w) key prec tw bw page) (B : L)
    (own : OwnsHeader X.birth.job.entry.result B)
    (a : (S).cutoff<((P).child c w).edges) :
    (preparedAfter M F p w X B own a).steps=
      (M.activeAfter p w X a).steps+
        (callReadFee prec X.birth.edge X.birth.dep X.birth.job.offset+5)+
        (F.layout p w X B own a).steps+(2*cw+4*q+5)+4 := by
  let taper := actual_path_taper T (.step p w) a
  change (sharedMachine M.modeWidth (F.fit (.step p w) a) taper.1 taper.2
    (readIncoming X B own) (F.layout p w X B own a) (M.activeAfter p w X a)).steps=_
  rw [(shared_setup_has_one_header_and_one_layout M.modeWidth (F.fit (.step p w) a)
    taper.1 taper.2 (readIncoming X B own) (F.layout p w X B own a) (M.activeAfter p w X a)).1,
    (incoming_words_from_published_head X B own).2.2]

/-! Execute this actual active entry with the original typed cached
child interpreter. Deeper subtrees in this particular comparison
are intentionally unchanged; the all-level scope closure is separate. -/
def activeEntryWithRealChildren (M : Machine) (F : AfterInputs T key prec tw bw page q cw)
    (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B)
    (a : (S).cutoff<((P).child c u).edges) :
    Meter (Block (T.frame (Path.step p u).reached) ell×L) :=
  let current := (P).child c u
  let path := Path.step p u
  let d := readyAtPath T path a
  let A := preparedAfter M F p u X B own a
  let mounted := mountResident X resident
  let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf
    (fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openBankDemand (M.demand X w) mounted.result retire
        (fun next live=>runCachedAfter M retire current path w next live)
        (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) B))
  ⟨(out.result,B),mounted.steps+A.steps+out.steps⟩

theorem mounted_real_active_entry_agrees (M : Machine) (F : AfterInputs T key prec tw bw page q cw)
    (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B)
    (a : (S).cutoff<((P).child c u).edges) :
    (activeEntryWithRealChildren M F retire p u X resident B own a).result=
      (runCachedAfter M retire c p u X resident B).result := by
  let current := (P).child c u
  let path := Path.step p u
  let d := readyAtPath T path a
  let A := preparedAfter M F p u X B own a
  let mounted := mountResident X resident
  let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
    let w := addressed (sel:=sel) d t z β g
    project (openBankDemand (M.demand X w) mounted.result retire
      (fun next live=>runCachedAfter M retire current path w next live)
      (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) B)
  let taper := actual_path_taper T path a
  have same := shared_active_value M.modeWidth (F.fit path a) taper.1 taper.2 (readIncoming X B own)
    (F.layout p u X B own a) (M.activeAfter p u X a)
    (reachable_positive T path.reached) T.vPositive hf read
  rw [runCachedAfter,dif_neg (Nat.not_le.mpr a)]
  exact congrArg (fun v : Block (T.frame path.reached) ell=>(v,B)) same

#print axioms mounted_real_active_entry_agrees

#print axioms physical_after_setup_charge
end
end J6R64Active

