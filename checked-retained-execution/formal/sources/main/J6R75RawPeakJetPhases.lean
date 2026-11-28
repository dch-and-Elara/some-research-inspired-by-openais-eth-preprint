import J6R75RawPeakJetFold

/-! Add the named half-jet of each existing raw ancestor without
replacing its prior mode/stock allowance or changing recursion. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.HermiteWeightScratch J6R68.RecursivePeak
open J6R50NonModeScratch J6R50Peak J6R52Peak J6R57ScopeFee J6R49NonModeStack
open J6R72SameRunRawScope J6R68.RetireScratch J6R51Peak J6R54PeakInput J6R66.BootPeak

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4500
set_option maxHeartbeats 6200000
set_option maxSynthPendingDepth 12

noncomputable section
attribute [local irreducible] J6R68ActiveInputs.Sweep.rawScheduleAt J6R72SameRunRawScope.rawReaderAt
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew width : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "JetCap" => (rawAncestorJetRoof s C ell f.natDegree (absolutePrecision s r.edges r.prec))

theorem one_same_raw_jet_supplement_extends_every_named_phase_cap
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (shared pageBound fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit M pageBound) (sizes : EntryWidths M fixed addr)
    (boot : BootBodyWidth M seed) (owners : OwnerWidth M owner)
    (p : Path sel r c) (named : ℕ)
    (stack : ActualRawAncestorStack M F chart E B own tails p named) :
    let room := rawCarrierRoof shared B r pageBound fixed addr seed owner s C q
    let reserve := pathLimit s C*JetCap
    ∃ extra,ActualRawJetSupplement M F chart E B own tails p named extra ∧
      recursiveResidentBits shared M B p named+extra≤room+reserve ∧
      ∀ currentCut previousRoof : ℕ,currentCut≤previousRoof →
        currentCut+extra≤previousRoof+reserve := by
  obtain ⟨extra,exactJets,jetFit⟩ :=
    existing_raw_stack_carries_its_same_suspended_half_jets M F chart E B own tails p named stack
  have base := raw_ancestor_and_same_physical_carrier_fit_together M F chart E B own tails
    shared pageBound fixed addr seed owner pageFit sizes boot owners p named stack
  exact ⟨extra,exactJets,Nat.add_le_add base jetFit,
    fun _ _ fit=>Nat.add_le_add fit jetFit⟩

#print axioms one_same_raw_jet_supplement_extends_every_named_phase_cap
end
end J6R75RawPeak
