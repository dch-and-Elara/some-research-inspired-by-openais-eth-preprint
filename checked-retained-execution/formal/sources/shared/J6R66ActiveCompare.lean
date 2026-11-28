import J6R66ActiveRun

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 4100
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Equality is of whole meters at each actual incoming-owner scope,
proved by the same physical child-edge decrease. Thus the R55/R56
ledger applies to the real new active runner rather than to a different
algorithm that happens to return the same arithmetic word. -/
namespace J6R66Active
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6R64Active J6R62ActivePrep J6R63Active
open J6R51Online J6R51ParentFrames J6R52CacheWhole J6R48RawRoute J6R54PeakInput J6R53PeakAddon
open J6ActiveSchedule J6R9Recursive J6R16ModeCost J6R21Ancestor J6R48DFS
open J6R10Repack J6R34ChildPath J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R26DescriptorTree J6R24MeteredRecursion J6R49DFS
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "Here" => (Path.root : Path sel r r)

theorem descendant_exact_meter
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L)
    (rootOwn : OwnsHeader E.header initial) (retire : J→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (B : L) (own : OwnsHeader X.birth.job.entry.result B) :
    runAfter M F retire c p u X resident B own=
      runCachedAfterSingleEmission (shadow M F E initial rootOwn) retire c p u X resident B := by
  let Q := shadow M F E initial rootOwn
  let relation := measure (fun x : Entered T key prec tw bw page=>x.call.edges)
  let motive (x : Entered T key prec tw bw page) : Prop :=
    runAfter M F retire x.parent x.path x.slot x.site x.resident x.bank x.owner=
      runCachedAfterSingleEmission Q retire x.parent x.path x.slot x.site x.resident x.bank
  have all (x : Entered T key prec tw bw page) : motive x := by
    refine relation.wf.induction (C:=motive) x ?_
    intro now ih
    rcases now with ⟨c,p,u,X,resident,B,own⟩
    change runAfter M F retire c p u X resident B own=
      runCachedAfterSingleEmission Q retire c p u X resident B
    let current := (P).child c u
    let path := Path.step p u
    by_cases stop : current.edges ≤ (S).cutoff
    · rw [stopped_after_uses_original_leaf M F retire p u X resident B own stop,
          runCachedAfterSingleEmission,dif_pos stop]
      rfl
    · let a := Nat.lt_of_not_ge stop
      let d := readyAtPath T path a
      let A := preparedAfter M F.live p u X B own a
      let A' := Q.activeAfter p u X a
      let mounted := mountResident X resident
      let hp := reachable_positive T path.reached
      let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
        let w := addressed (sel:=sel) d t z β g
        project (openOnce (M.demand X w) mounted.result retire
          (fun next=>runAfter M F retire current path w next)
          (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) B)
      let prev : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
        let w := addressed (sel:=sel) d t z β g
        project (openBankDemandSingleEmission (M.demand X w) mounted.result retire
          (fun next live=>runCachedAfterSingleEmission Q retire current path w next live)
          (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) B)
      have same : read=prev := by
        funext t z β g
        let w := addressed (sel:=sel) d t z β g
        let low := T.bank (registerPrecision S current t) (register_positive d t)
        let bad : Meter (Block low ell) := zeroM low.hp
        let go := fun next=>runAfter M F retire current path w next
        let older := fun next live=>runCachedAfterSingleEmission Q retire current path w next live
        change project (openOnce (M.demand X w) mounted.result retire go bad B)=
          project (openBankDemandSingleEmission (M.demand X w) mounted.result retire older bad B)
        rw [open_once_same_full_meter (M.demand X w) mounted.result retire go older bad B]
        intro next live cur yes
        let x : Entered T key prec tw bw page := ⟨current,path,w,next,live,cur,yes⟩
        exact ih x ((P).smaller current w)
      have samePrep : A=A' := real_preparation_is_exact_header_normal_form M F p u X B own a
      rw [active_after_receives_current_header M F retire p u X resident B own a,
          runCachedAfterSingleEmission,dif_neg stop]
      let out := A.result.eval M.modeWidth hp T.vPositive hf read
      let old := A'.result.eval M.modeWidth hp T.vPositive hf prev
      change (⟨(out.result,B),mounted.steps+A.steps+out.steps⟩ : Meter _) =
        ⟨(old.result,B),mounted.steps+A'.steps+old.steps⟩
      have eqOut : out=old := by
        change A.result.eval M.modeWidth hp T.vPositive hf read=
          A'.result.eval M.modeWidth hp T.vPositive hf prev
        rw [samePrep,same]
      rw [samePrep,eqOut]
  exact all ⟨c,p,u,X,resident,B,own⟩

theorem same_actual_root_meter
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial) :
    runRoot M F E retire initial own=
      runCachedRootSingleEmission (shadow M F E initial own) retire initial := by
  let Q := shadow M F E initial own
  by_cases stop : r.edges ≤ (S).cutoff
  · rw [runRoot,dif_pos stop,runCachedRootSingleEmission,dif_pos stop]
    rfl
  · let a := Nat.lt_of_not_ge stop
    let d := readyAtPath T Here a
    let A := rootSetup M F E initial own a
    let hp := reachable_positive T (Here).reached
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (bootWithHeader (M.initial w) retire (runAfter M F retire r Here w)
        (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) initial)
    let prev := rootReadSingleEmission Q retire initial a
    have same : read=prev := by
      funext t z β g
      let w := addressed (sel:=sel) d t z β g
      let low := T.bank (registerPrecision S r t) (register_positive d t)
      let bad : Meter (Block low ell) := zeroM low.hp
      let go := runAfter M F retire r Here w
      let prior := runCachedAfterSingleEmission Q retire r Here w
      change project (bootWithHeader (M.initial w) retire go bad initial)=
        project (bootBankDemand (M.initial w) retire prior bad initial)
      rw [boot_header_same_full_meter (M.initial w) retire go prior bad initial]
      intro next live cur yes
      exact descendant_exact_meter M F E initial own retire r Here w next live cur yes
    rw [runRoot,dif_neg stop,runCachedRootSingleEmission,dif_neg stop]
    let work := A.result.eval M.modeWidth hp T.vPositive hf
    change (⟨((work read).result,initial),A.steps+(work read).steps⟩ : Meter _) =
      ⟨((work prev).result,initial),A.steps+(work prev).steps⟩
    rw [same]

#print axioms descendant_exact_meter
#print axioms same_actual_root_meter
end
end J6R66Active

