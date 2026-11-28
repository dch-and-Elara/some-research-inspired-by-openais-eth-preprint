import J6R75RawPeakLayerCap
import J6R50PeakStartPrecision

/-! Fold only the actual raw-parent witnesses along the physical
occurrence path. The same issued stock and literal child callback
remain part of each record. The witness is not an executable history
or a list physically stored by the interpreter. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.HermiteWeightScratch J6R68.RecursivePeak
open J6R50NonModeScratch J6R50Peak J6R52Peak J6R57ScopeFee
open J6R72SameRunRawScope J6R68.RetireScratch

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4500
set_option maxHeartbeats 6500000
set_option maxSynthPendingDepth 12

noncomputable section
attribute [local irreducible] J6R68ActiveInputs.Sweep.rawScheduleAt J6R72SameRunRawScope.rawReaderAt
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew width : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def SelectedAncestorAt (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (w : (P).Slot c) (bits : ℕ) : Prop :=
  let d := readyAtPath T p w.property
  let hp := reachable_positive T p.reached
  ∃ (D : Schedule sel d T.bank q) (child : ActiveChild (sel:=sel) (d:=d) T.bank),
    D=(rawScheduleAt M F chart E B own p w.property).result ∧
    child=rawReaderAt M F chart (retireSavedDirectory tails) B p w.property ∧
    ∃ (x : D.EmitRow) (z : Probe S c) (β : NativeMenu (N sel) c (D.tag x)) (g : Fin 64),
      addressed (sel:=sel) d (D.tag x) z β g=w ∧
      let obs := observedRawReader M F chart tails B p w.property (D.tag x) z β g
      let run := emittedCentreMeter D M.modeWidth hp T.vPositive hf child
      project obs.1=child (D.tag x) z β g ∧ obs.2=some ⟨tails,tails⟩ ∧
      obs.1.result.2=stackBank (borns M) B p ∧
      ∃ (mode : NativeSuspension (C:=C) (sel:=sel) c) (pre post : List D.EmitRow),
        SawEmittedProbe d D M.modeWidth T.vPositive child x z β g mode ∧
        actualEmittedCentreRows D=pre++x::post ∧
        D.highRun M.modeWidth hp T.vPositive hf child=resumeUV (D.high hp).hp (pre.map run)
          (addM (D.high hp).hp (run x) (sumM (D.high hp).hp run post)) ∧
        bits=selectedParentBits d D M.modeWidth hp T.vPositive hf child mode pre

theorem explicit_raw_parent_yields_the_selected_ancestor
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (legal : ReadyOnStack (borns M) B) (fits : q≤uniformWidth s C)
    (p : Path sel r c) (w : (P).Slot c)
    (D : Schedule sel (readyAtPath T p w.property) T.bank q)
    (child : ActiveChild (sel:=sel) (d:=readyAtPath T p w.property) T.bank)
    (issued : D=(rawScheduleAt M F chart E B own p w.property).result)
    (callback : child=rawReaderAt M F chart (retireSavedDirectory tails) B p w.property) :
    ∃ bits,SelectedAncestorAt M F chart E B own tails p w bits := by
  let d := readyAtPath T p w.property
  obtain ⟨x,z,β,g,slotEq⟩ := every_native_slot_is_addressed_by_a_literal_raw_row d D w
  obtain ⟨_,meter,tail,bank,mode,pre,post,pulse,order,resumeFold,_⟩ :=
    actual_raw_layer_binds_source_prior_rows_and_live_group M F chart E B own tails
      legal fits p w.property D child issued callback x z β g
  exact ⟨_,D,child,issued,callback,x,z,β,g,slotEq,meter,tail,bank,mode,pre,post,pulse,order,resumeFold,rfl⟩

theorem actual_raw_parent_yields_the_selected_ancestor
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (legal : ReadyOnStack (borns M) B) (fits : q≤uniformWidth s C)
    (p : Path sel r c) (w : (P).Slot c) :
    ∃ bits,SelectedAncestorAt M F chart E B own tails p w bits := by
  let live : Schedule sel (readyAtPath T p w.property) T.bank q :=
    (rawScheduleAt M F chart E B own p w.property).result
  let read : ActiveChild (sel:=sel) (d:=readyAtPath T p w.property) T.bank :=
    rawReaderAt M F chart (retireSavedDirectory tails) B p w.property
  exact explicit_raw_parent_yields_the_selected_ancestor M F chart E B own tails legal fits
    p w live read rfl rfl

inductive ActualRawAncestorStack (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → Prop where
  | root : ActualRawAncestorStack M F chart E B own tails (.root : Path sel r r) 0
  | enter {x : Call (PhysicalHost f ell)} {p : Path sel r x} {old layer : ℕ}
      (earlier : ActualRawAncestorStack M F chart E B own tails p old) (w : (P).Slot x)
      (event : SelectedAncestorAt M F chart E B own tails p w layer) :
      ActualRawAncestorStack M F chart E B own tails (.step p w) (old+layer)

theorem all_physical_raw_paths_have_the_same_selected_ancestor_stack
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (legal : ReadyOnStack (borns M) B) (fits : q≤uniformWidth s C)
    (p : Path sel r c) :
    ∃ bits,ActualRawAncestorStack M F chart E B own tails p bits := by
  induction p with
  | root => exact ⟨0,.root⟩
  | step p w ih =>
    obtain ⟨used, prior⟩ := ih
    obtain ⟨b,one⟩ := actual_raw_parent_yields_the_selected_ancestor M F chart E B own tails legal fits p w
    exact ⟨used+b,.enter prior w one⟩

#print axioms explicit_raw_parent_yields_the_selected_ancestor
#print axioms actual_raw_parent_yields_the_selected_ancestor
#print axioms all_physical_raw_paths_have_the_same_selected_ancestor_stack
end
end J6R75RawPeak
