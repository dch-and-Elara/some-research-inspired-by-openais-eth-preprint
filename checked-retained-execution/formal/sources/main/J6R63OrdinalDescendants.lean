import J6R63OrdinalProgram

/-! One ranked descendant runner. It actually consumes the words of
each inside-pulse callback to acquire a checked local child packet,
then uses the original single-emission scoped transition. The root
boot and stopping leaf operations are the previous source operations.
The computational interface has no old demand or whole tuple menu. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
open J6R51ParentFrames J6R51Online J6R52CacheWhole J6R54PeakInput
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4900
set_option maxHeartbeats 12500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "PlanAt" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Here" => (Path.root : Path sel r r)

variable {B : Base T key prec tw bw page (q+1)}

abbrev RecursiveAt {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c) :=
  (w : (@Plan f ell s sel).Slot ((@Plan f ell s sel).child c u)) →
  (next : StoredSite T ((Path.step p u).ticket w) key prec tw bw page) →
  ResidentBank next → SM L (Block (T.frame (Path.step (Path.step p u) w).reached) ell)

def rankedDescendantStep (D : Program B b) (retire : J→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (PlanAt).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X)
    (continueAt : RecursiveAt (T:=T) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (page:=page) p u) :
    SM L (Block (T.frame (Path.step p u).reached) ell) :=
  let current := (PlanAt).child c u
  let path := Path.step p u
  if stop : current.edges≤(SP).cutoff then
    fun bank=>
      let v := B.leafAfter p u X stop bank
      ⟨(v.result,bank),v.steps⟩
  else
    let on := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel path.reached T.rootStable on
    let A := B.activeAfter p u X on
    fun bank=>
      let cached := mountResident X resident
      let out := rankedActive A.result (centreArchiveOrdinal T path on) B.modeWidth D.ordinalWidth
        (reachable_positive T path.reached) T.vPositive hf (D.archive p u X on)
        (fun t z β raw i rawExact rankExact g=>
          let w := addressed (sel:=sel) d t z β g
          let request := D.prepare p u X cached.result on t z β g raw
          let trueRank := rankExact.trans (centre_archive_word_is_original_ticket_ordinal T path on t z β g)
          let loaded := acceptCurrent request raw i rawExact trueRank
          project (openBankDemandSingleEmission loaded cached.result retire
            (continueAt w)
            (zeroM (T.bank (registerPrecision SP current t) (register_positive d t)).hp) bank))
      ⟨(out.result,bank),cached.steps+A.steps+out.steps⟩

def runFrom (D : Program B b) (retire : J→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (resident : ResidentBank X) :
    SM L (Block (T.frame (Path.step p u).reached) ell) :=
  rankedDescendantStep D retire c p u X resident
    (fun w next live => runFrom D retire ((@Plan f ell s sel).child c u) (Path.step p u) w next live)
termination_by ((@Plan f ell s sel).child c u).edges
decreasing_by exact (@Plan f ell s sel).smaller ((@Plan f ell s sel).child c u) w

theorem ranked_runner_restores_the_same_parent_bank
    (D : Program B b) (retire : J→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (PlanAt).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (live : ResidentBank X) (bank : L) :
    (runFrom D retire c p u X live bank).result.2=bank := by
  by_cases stop : ((PlanAt).child c u).edges≤(SP).cutoff
  · rw [runFrom,rankedDescendantStep,dif_pos stop]
  · rw [runFrom,rankedDescendantStep,dif_neg stop]

#print axioms rankedDescendantStep
#print axioms runFrom
#print axioms ranked_runner_restores_the_same_parent_bank
end
end J6R63Ordinal
