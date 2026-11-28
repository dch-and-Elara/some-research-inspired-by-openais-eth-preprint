import J6R66ActivePlan
import J6R66ActiveScope
import J6R54PeakInputRootRunner

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 21000000
set_option maxRecDepth 3800
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Same R54 one-emission recursion, in which every successful scope
supplies its true live incoming header to the new active preparer.
The separate exterior seed is read from the actual initial bank. -/
namespace J6R66Active
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6R63Active J6R62ActivePrep J6R64Active
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

/-- Package every dependent current field in a single WF argument.
The accessibility proof is erased; no executable fuel counter or
phantom future child is inserted into the Meter. -/
structure Entered
    (T : Prepared cfg sel r hf) (key prec tw bw page : ℕ) where
  parent : Call (PhysicalHost f ell)
  path : Path sel r parent
  slot : (P).Slot parent
  site : StoredSite T (path.ticket slot) key prec tw bw page
  resident : ResidentBank site
  bank : PageBank f ell key prec tw bw page
  owner : OwnsHeader site.birth.job.entry.result bank

abbrev Entered.call (x : Entered T key prec tw bw page) := (P).child x.parent x.slot

abbrev EntryOut (x : Entered T key prec tw bw page) :=
  Meter (Block (T.frame (Path.step x.path x.slot).reached) ell×L)

def stateBody (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (retire : J→ℕ) (x : Entered T key prec tw bw page)
    (recur : (ys : Entered T key prec tw bw page) → ys.call.edges<x.call.edges → EntryOut ys) :
    EntryOut x :=
  let current := x.call
  let path := Path.step x.path x.slot
  if stop : current.edges ≤ (S).cutoff then
    let w := M.leafAfter x.path x.slot x.site stop x.bank
    ⟨(w.result,x.bank),w.steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let d := readyAtPath T path active
    let A := preparedAfter M F.live x.path x.slot x.site x.bank x.owner active
    let mounted := mountResident x.site x.resident
    let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf
      (fun t z β g=>
        let w := addressed (sel:=sel) d t z β g
        let acquire := M.demand x.site w
        project (openOnce acquire mounted.result retire
          (fun next live bank owner =>
            recur ⟨current,path,w,next,live,bank,owner⟩ ((P).smaller current w))
          (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) x.bank))
    ⟨(out.result,x.bank),mounted.steps+A.steps+out.steps⟩

def runState (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (retire : J→ℕ)
    (x : Entered T key prec tw bw page) : EntryOut x :=
  (measure (fun y : Entered T key prec tw bw page=>y.call.edges)).wf.fix
    (stateBody M F retire) x

theorem run_state_equation (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (retire : J→ℕ) (x : Entered T key prec tw bw page) :
    runState M F retire x=stateBody M F retire x (fun y _=>runState M F retire y) := by
  exact WellFounded.fix_eq _ _ _

def runAfter (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (retire : J→ℕ) (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B) :
    Meter (Block (T.frame (Path.step p u).reached) ell×L) :=
  runState M F retire ⟨c,p,u,X,resident,B,own⟩

theorem stopped_after_uses_original_leaf (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B)
    (stop : ((P).child c u).edges≤(S).cutoff) :
    runAfter M F retire c p u X resident B own=
      ⟨((M.leafAfter p u X stop B).result,B),(M.leafAfter p u X stop B).steps⟩ := by
  unfold runAfter
  rw [run_state_equation]
  dsimp only [stateBody]
  rw [dif_pos stop]

theorem active_after_receives_current_header (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B)
    (a : (S).cutoff<((P).child c u).edges) :
    let current := (P).child c u
    let path := Path.step p u
    let d := readyAtPath T path a
    let A := preparedAfter M F.live p u X B own a
    let mounted := mountResident X resident
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openOnce (M.demand X w) mounted.result retire
        (fun next=>runAfter M F retire current path w next)
        (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) B)
    let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf read
    runAfter M F retire c p u X resident B own=⟨(out.result,B),mounted.steps+A.steps+out.steps⟩ := by
  dsimp only
  change runState M F retire (⟨c,p,u,X,resident,B,own⟩ : Entered T key prec tw bw page)=_
  rw [run_state_equation]
  dsimp only [stateBody]
  rw [dif_neg (Nat.not_le.mpr a)]
  rfl

theorem active_after_restores (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (retire : J→ℕ) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B) :
    (runAfter M F retire c p u X resident B own).result.2=B := by
  by_cases stop : ((P).child c u).edges ≤ (S).cutoff
  · rw [stopped_after_uses_original_leaf M F retire p u X resident B own stop]
  · rw [active_after_receives_current_header M F retire p u X resident B own (Nat.lt_of_not_ge stop)]

def runRoot (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (B : L) (own : OwnsHeader E.header B) :
    Meter (Block (T.frame (Here).reached) ell×L) :=
  if stop : r.edges ≤ (S).cutoff then
    let leaf := M.leafRoot stop B
    ⟨(leaf.result,B),leaf.steps⟩
  else
    let a := Nat.lt_of_not_ge stop
    let d := readyAtPath T Here a
    let A := rootSetup M F E B own a
    let out := A.result.eval M.modeWidth (reachable_positive T (Here).reached) T.vPositive hf
      (fun t z β g=>
        let w := addressed (sel:=sel) d t z β g
        project (bootWithHeader (M.initial w) retire (runAfter M F retire r Here w)
          (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) B))
    ⟨(out.result,B),A.steps+out.steps⟩

theorem root_restores_actual_bank (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (B : L) (own : OwnsHeader E.header B) :
    (runRoot M F E retire B own).result.2=B := by
  by_cases stop : r.edges ≤ (S).cutoff
  · rw [runRoot,dif_pos stop]
  · rw [runRoot,dif_neg stop]

#print axioms runRoot
#print axioms root_restores_actual_bank

#print axioms run_state_equation
#print axioms stopped_after_uses_original_leaf
#print axioms runAfter
#print axioms active_after_restores
#print axioms active_after_receives_current_header
end
end J6R66Active

