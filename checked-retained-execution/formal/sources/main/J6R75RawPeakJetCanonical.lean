import J6R75RawPeakJetPhases

/-! A named half-jet on a fixed actual occurrence has a unique encoded width.
Neither a second evaluation nor selection of a new runtime stock is needed:
the emitted row with the actual centre key is unique. -/
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
set_option maxHeartbeats 6900000
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

def exactHalfJetWidth (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (w : (P).Slot c) : ℕ :=
  let D := (rawScheduleAt M F chart E B own p w.property).result
  let x := Classical.choose (D.tag_surj w.val.1)
  (w.val.2.1.val+2)*((D.fetch x).window*(ell*(f.natDegree*registerPrecision S c (D.tag x))))

theorem observed_half_jet_has_its_actual_unique_width
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (w : (P).Slot c) (named extra : ℕ)
    (h : SelectedHalfJetAt M F chart E B own tails p w named extra) :
    extra=exactHalfJetWidth M F chart E B own p w := by
  obtain ⟨D,child,issued,_,x,z,β,g,slotEq,_,_,_,_,_,_,_,size⟩ := h
  have ht : D.tag x=w.val.1 := congrArg (fun u : (P).Slot c=>u.val.1) slotEq
  have hz : z=w.val.2.1 := congrArg (fun u : (P).Slot c=>u.val.2.1) slotEq
  have numbered := (actual_emitted_row_has_the_same_suspended_jet_width
    p w.property D M.modeWidth T.vPositive child x z).2.1
  refine size.trans (numbered.trans ?_)
  subst D
  let A := (rawScheduleAt M F chart E B own p w.property).result
  have hx : x=Classical.choose (A.tag_surj w.val.1) :=
    A.tag_inj (ht.trans (Classical.choose_spec (A.tag_surj w.val.1)).symm)
  change (z.val+2)*((A.fetch x).window*(ell*(f.natDegree*registerPrecision S c (A.tag x))))=
     exactHalfJetWidth M F chart E B own p w
  rw [hz,hx]
  rfl

def exactAncestorJetWidth (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) : {u : Call (PhysicalHost f ell)} → Path sel r u → ℕ
  | _,.root=>0
  | _,.step p w=>exactAncestorJetWidth M F chart E B own p+exactHalfJetWidth M F chart E B own p w

theorem observed_ancestor_jet_width_is_canonical
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (named extra : ℕ)
    (h : ActualRawJetSupplement M F chart E B own tails p named extra) :
    extra=exactAncestorJetWidth M F chart E B own p := by
  induction h with
  | root=>rfl
  | @enter x p used more part supplement earlier w old jet ih=>
    exact congrArg₂ (·+·) ih (observed_half_jet_has_its_actual_unique_width
      M F chart E B own tails p w part supplement jet)

theorem exact_raw_ancestor_jet_width_fits_and_is_observed
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (named : ℕ)
    (h : ActualRawAncestorStack M F chart E B own tails p named) :
    let j := exactAncestorJetWidth M F chart E B own p
    ActualRawJetSupplement M F chart E B own tails p named j ∧
      j≤pathLimit s C*rawAncestorJetRoof s C ell f.natDegree (absolutePrecision s r.edges r.prec) := by
  obtain ⟨extra,jets,fit⟩ :=
    existing_raw_stack_carries_its_same_suspended_half_jets M F chart E B own tails p named h
  have equal := observed_ancestor_jet_width_is_canonical M F chart E B own tails p named extra jets
  exact ⟨equal ▸ jets,equal ▸ fit⟩

#print axioms observed_half_jet_has_its_actual_unique_width
#print axioms observed_ancestor_jet_width_is_canonical
#print axioms exact_raw_ancestor_jet_width_fits_and_is_observed
end
end J6R75RawPeak
