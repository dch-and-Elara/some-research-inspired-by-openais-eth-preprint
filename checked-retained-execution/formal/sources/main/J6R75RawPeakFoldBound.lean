import J6R75RawPeakFold

/-! The selected ancestor payload built above is summed on the same
physical path. Each layer's high word comes from that raw stock's
exact margin, not from a new global rate or default precision. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R22Active J6R9Recursive A1R12
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.HermiteWeightScratch J6R68.RecursivePeak
open J6R50NonModeScratch J6R50Peak J6R52Peak J6R57ScopeFee
open J6R72SameRunRawScope J6R68.RetireScratch J6R68ActiveInputs

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
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "Lo" => (absolutePrecision s r.edges r.prec)
local notation "Hi" => (absoluteHighCap s C (absolutePrecision s r.edges r.prec))
local notation "Cap" => (selectedRawLayerRoof s C q ell f.natDegree
  (absolutePrecision s r.edges r.prec) (absoluteHighCap s C (absolutePrecision s r.edges r.prec)))

theorem raw_issued_margin_has_the_absolute_printed_high_word
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (D : Schedule sel (readyAtPath T p a) T.bank q) :
    c.prec+D.extra≤Hi := by
  have hp := absolute_inherited_precision_cap cfg sel T.rootStable p
  have hM := actual_edges_uniform T p
  obtain ⟨hu,span⟩ := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ p.reached a
  have axis : (S).levelBits c.depth≤Nat.clog 2 s := bits_le_lam _ _
  have loss := simple_common_scale_cap axis hu span
  unfold Schedule.extra
  rw [D.marginExact]
  exact Nat.add_le_add hp (loss.trans (Nat.mul_le_mul_right (commonSlope s) hM))

theorem observed_raw_parent_bits_fit_uniform_selected_cap
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (w : (P).Slot c) (n : ℕ)
    (seen : SelectedAncestorAt M F chart E B own tails p w n) :
    n≤Cap := by
  obtain ⟨D,child,_,_,x,z,β,g,_,_,_,_,mode,pre,post,_,order,_,bits⟩ := seen
  have len : (actualEmittedCentreRows D).length=D.stock.rows.length := by
    simp only [actualEmittedCentreRows,List.length_pmap]
  have pref : pre.length≤D.stock.rows.length := by
    rw [order,List.length_append] at len
    exact (Nat.le_add_right _ _).trans_eq len
  rw [bits]
  exact selected_raw_parent_fields_fit_the_absolute_layer_roof p w.property D M.modeWidth
    (reachable_positive T p.reached) T.vPositive child mode pre Hi
    (raw_issued_margin_has_the_absolute_printed_high_word p w.property D) pref

theorem actual_raw_ancestor_stack_selected_words_fit_one_reserve_per_move
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (bits : ℕ)
    (stack : ActualRawAncestorStack M F chart E B own tails p bits) :
    bits≤pathLimit s C*Cap := by
  have usedCap : bits≤moves p*Cap := by
    induction stack with
    | root => exact Nat.zero_le _
    | @enter x p old one earlier w event ih =>
      have cap := observed_raw_parent_bits_fit_uniform_selected_cap M F chart E B own tails p w one event
      simpa only [moves,Nat.add_mul,Nat.one_mul] using Nat.add_le_add ih cap
  exact usedCap.trans (Nat.mul_le_mul_right _ (actual_ancestry_moves_any_start cfg sel T.rootStable p))

theorem every_raw_path_has_a_named_suspended_ancestor_budget
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (legal : ReadyOnStack (borns M) B) (fits : q≤uniformWidth s C)
    (p : Path sel r c) :
    ∃ bits,ActualRawAncestorStack M F chart E B own tails p bits ∧ bits≤pathLimit s C*Cap := by
  obtain ⟨bits,observed⟩ := all_physical_raw_paths_have_the_same_selected_ancestor_stack M F chart E B own tails
    legal fits p
  exact ⟨bits,observed,actual_raw_ancestor_stack_selected_words_fit_one_reserve_per_move M F chart E B own tails
    p bits observed⟩

#print axioms raw_issued_margin_has_the_absolute_printed_high_word
#print axioms actual_raw_ancestor_stack_selected_words_fit_one_reserve_per_move
#print axioms every_raw_path_has_a_named_suspended_ancestor_budget
end
end J6R75RawPeak
