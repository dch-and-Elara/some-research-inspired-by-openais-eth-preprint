import J6R75RawPeakJet
import J6R75RawPeakCarry

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
open J6R72SameRunRawScope J6R68.RetireScratch

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

def SelectedHalfJetAt (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (w : (P).Slot c) (named extra : ℕ) : Prop :=
  let d := readyAtPath T p w.property
  ∃ (D : Schedule sel d T.bank q) (child : ActiveChild (sel:=sel) (d:=d) T.bank),
    D=(rawScheduleAt M F chart E B own p w.property).result ∧
    child=rawReaderAt M F chart (retireSavedDirectory tails) B p w.property ∧
    ∃ (x : D.EmitRow) (z : Probe S c) (β : NativeMenu (N sel) c (D.tag x)) (g : Fin 64),
      addressed (sel:=sel) d (D.tag x) z β g=w ∧
      ∃ (mode : NativeSuspension (C:=C) (sel:=sel) c) (pre post : List D.EmitRow),
        SawEmittedProbe d D M.modeWidth T.vPositive child x z β g mode ∧
        actualEmittedCentreRows D=pre++x::post ∧
        named=selectedParentBits d D M.modeWidth (reachable_positive T p.reached)
          T.vPositive hf child mode pre ∧
        let pause := observedRawHalfJet d D M.modeWidth T.vPositive child x z
        (D.fetch x).centreJet M.modeWidth T.vPositive (child (D.tag x))=pause.2 ∧
        extra=pause.1.length

theorem augment_the_same_ancestor_cut_with_its_half_jet
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (w : (P).Slot c) (named : ℕ)
    (seen : SelectedAncestorAt M F chart E B own tails p w named) :
    ∃ extra,SelectedHalfJetAt M F chart E B own tails p w named extra ∧ extra≤JetCap := by
  obtain ⟨D,child,issued,callback,x,z,β,g,slotEq,_,_,_,mode,pre,post,pulse,order,_,hb⟩ := seen
  obtain ⟨resumes,_,bound⟩ :=
    actual_emitted_row_has_the_same_suspended_jet_width p w.property D M.modeWidth T.vPositive child x z
  exact ⟨_,⟨D,child,issued,callback,x,z,β,g,slotEq,mode,pre,post,pulse,order,hb,resumes,rfl⟩,bound⟩

inductive ActualRawJetSupplement (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → ℕ → Prop where
  | root : ActualRawJetSupplement M F chart E B own tails (.root : Path sel r r) 0 0
  | enter {x : Call (PhysicalHost f ell)} {p : Path sel r x} {used more part extra : ℕ}
      (earlier : ActualRawJetSupplement M F chart E B own tails p used more) (w : (P).Slot x)
      (old : SelectedAncestorAt M F chart E B own tails p w part)
      (jet : SelectedHalfJetAt M F chart E B own tails p w part extra) :
      ActualRawJetSupplement M F chart E B own tails (.step p w) (used+part) (more+extra)

theorem existing_raw_stack_carries_its_same_suspended_half_jets
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (named : ℕ)
    (stack : ActualRawAncestorStack M F chart E B own tails p named) :
    ∃ extra,ActualRawJetSupplement M F chart E B own tails p named extra ∧ extra≤pathLimit s C*JetCap := by
  have perMove : ∃ extra,ActualRawJetSupplement M F chart E B own tails p named extra ∧ extra≤moves p*JetCap := by
    induction stack with
    | root => exact ⟨0,.root,Nat.zero_le _⟩
    | @enter x p old bits earlier w event ih =>
      obtain ⟨n,smaller,fit⟩ := ih
      obtain ⟨j,one,bound⟩ := augment_the_same_ancestor_cut_with_its_half_jet M F chart E B own tails p w bits event
      refine ⟨n+j,.enter smaller w event one,?_⟩
      simpa only [moves,Nat.add_mul,Nat.one_mul] using Nat.add_le_add fit bound
  obtain ⟨extra,got,fit⟩ := perMove
  exact ⟨extra,got,fit.trans (Nat.mul_le_mul_right _ (actual_ancestry_moves_any_start cfg sel T.rootStable p))⟩

/-- Pure addition of a separately established cut cap; the witness
identifies the retained jets on that same ancestor chain. -/
theorem add_half_jet_reserve_to_a_named_same_raw_phase
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (named phase room : ℕ)
    (stack : ActualRawAncestorStack M F chart E B own tails p named) (fit : phase≤room) :
    ∃ extra,ActualRawJetSupplement M F chart E B own tails p named extra ∧
      phase+extra≤room+pathLimit s C*JetCap := by
  obtain ⟨extra,seen,bound⟩ := existing_raw_stack_carries_its_same_suspended_half_jets
    M F chart E B own tails p named stack
  exact ⟨extra,seen,Nat.add_le_add fit bound⟩

#print axioms augment_the_same_ancestor_cut_with_its_half_jet
#print axioms existing_raw_stack_carries_its_same_suspended_half_jets
#print axioms add_half_jet_reserve_to_a_named_same_raw_phase
end
end J6R75RawPeak
