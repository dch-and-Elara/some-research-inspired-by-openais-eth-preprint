import J6R75RawPeakCarryScopes
import J6R75RawPeakJetPhases

/-! One real publish/mount/retire transaction preserves the actual
half-jet reserve chosen for that same entered child. No companion
evaluation is used; the numerical additional reserve is charged
once across the maximum of the named cuts. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.RecursivePeak J6R66.BootPeak
open J6R50Peak J6R51Peak J6R52Peak J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R57ScopeFee
open J6R68.RetireScratch J6R68.MountFilterScratch J6R72SameRunLocalPeak J6R72SameRunRawScope
open J6R51ParentFrames J6R52CacheWhole J6R52CacheSource J6R25PreparedSupply

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4700
set_option maxHeartbeats 6200000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew width : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "JetReserve" => (pathLimit s C*rawAncestorJetRoof s C ell f.natDegree (absolutePrecision s r.edges r.prec))

def SameRawScopeWithJets
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (B : L) (tails : SavedDirectoryTails width)
    (shared pageBound fixed addr seed owner : ℕ) (p : Path sel r c) (w : (P).Slot c)
    (carry extra : ℕ) : Prop :=
  let a := w.property
  let t := w.val.1
  let z := w.val.2.1
  let β := w.val.2.2.1
  let g := w.val.2.2.2
  let obs := observedRawReader M F chart tails B p a t z β g
  let roof := rawCarrierRoof shared B r pageBound fixed addr seed owner s C q
  let room := roof+max ((2*(C*s))*(addr+sourceBodyCap s C seed)) (4*width)+JetReserve
  project obs.1=rawReaderAt M F chart (retireSavedDirectory tails) B p a t z β g ∧
    obs.2=some ⟨tails,tails⟩ ∧ obs.1.result.2=stackBank (borns M) B p ∧
  trueRawReturnWithCarry M B p w shared carry ⟨tails,tails⟩+extra≤room ∧
  (∀ point,recursiveStagingBits M B p w shared carry point+extra≤roof+JetReserve) ∧
  (∀ (_active : (S).cutoff<((P).child c w).edges) (j n : ℕ) (point : ChildWritePoint),
    let x := sourceEntered M B p w
    let picked := observeSelection x.site.birth.native.gWord j x.site.birth.native.physical.raw
    let wrote := framesFromSelected x.site.site x.resident.rows picked.1.result
    (mountResident x.site x.resident).steps=picked.1.steps+wrote.steps+10 ∧
    max (recursiveStagingBits M B p w shared carry point)
      (max (max (filterBits M B p w shared carry j) (framePrefixBits M B p w shared carry n))
        (trueRawReturnWithCarry M B p w shared carry (⟨tails,tails⟩ : TailCopyObservation width)))+extra≤room)

theorem actual_raw_scope_cuts_keep_the_fixed_ancestor_half_jets
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (legal : ReadyOnStack (borns M) B)
    (shared pageBound fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit M pageBound) (sizes : EntryWidths M fixed addr)
    (boot : BootBodyWidth M seed) (owners : OwnerWidth M owner)
    (p : Path sel r c) (w : (P).Slot c) (carry extra : ℕ)
    (seen : ActualRawAncestorStack M F chart E B own tails (.step p w) carry)
    (bounded : extra≤JetReserve) :
    SameRawScopeWithJets M F chart B tails shared pageBound fixed addr seed owner p w carry extra := by
  rcases w with ⟨⟨t,z,β,g⟩,a⟩
  obtain ⟨read,tailsFound,stateFound,ret,pub,mount⟩ :=
    real_raw_child_scope_phases_keep_one_and_the_same_ancestor_payload M F chart E B own tails legal
      shared pageBound fixed addr seed owner pageFit sizes boot owners p a t z β g carry seen
  refine ⟨read,tailsFound,stateFound,Nat.add_le_add ret bounded,
    fun pt=>Nat.add_le_add (pub pt) bounded,?_⟩
  intro act j n point
  obtain ⟨fee,cap⟩ := mount act j n point
  exact ⟨fee,Nat.add_le_add cap bounded⟩

#print axioms actual_raw_scope_cuts_keep_the_fixed_ancestor_half_jets
end
end J6R75RawPeak
