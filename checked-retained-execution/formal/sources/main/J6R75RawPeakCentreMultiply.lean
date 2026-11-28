import J6R75RawPeakAggregate
import J6R70HermiteScratch
import J6R68HermiteWeightScratchRawInverse

/-! R70 retained input/weight and convolution arrays at the actual
raw D.fetch x weighted term, not a postulated equal-valued callback. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active J6R9Recursive J6R19Retained J6R21Leaf
open J6R23ScheduleWeight J6R49NonModeStack J6R50NonModeScratch J6R68.HermiteWeightScratch J6R68ActiveInputs
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.RecursivePeak J6R66.BootPeak
open J6R50Peak J6R51Peak J6R52Peak J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R57ScopeFee
open J6R68.RetireScratch J6R72SameRunRawScope
open J6R51ParentFrames J6R52CacheWhole J6R52CacheSource J6R25PreparedSupply

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4700
set_option maxHeartbeats 12500000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew width : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)

open J6R70HermiteScratch

def NamedRawWeightedTermMultiply
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (D : Schedule sel (readyAtPath T p a) T.bank q) (x : D.EmitRow)
    (hq : 0<q) (child : ActiveChild (sel:=sel) (d:=readyAtPath T p a) T.bank)
    (j : ℕ) (head : UBlock (D.high (reachable_positive T p.reached)).words)
    (suffix : List (UBlock (D.high (reachable_positive T p.reached)).words))
    (resident roof : ℕ) : Prop :=
  let hp := reachable_positive T p.reached
  let hv := T.vPositive
  let J := D.fetch x
  let high := D.high hp
  let t := (D.tag x).val
  let A := (S).levelBits c.depth
  let jet := J.centreJet hq hv (child (D.tag x))
  let eq := (J.low.natDegree hf).trans (high.natDegree hf).symm
  let step := J.centreTerm hv hf high D.extra jet.result
  let saved := ((List.range J.window).take j).map step
  let kept := scalarTermsPayload saved ++ jetPayload jet.result
  let coeff := jetCoeffM J.low.hp J.low.sizePos jet.result j
  let lifted := resizeUV eq coeff.result
  let weight := rawWeight high.hp high.sizePos hv A D.extra j t J.roster.rows
  let operands := multiplyOperands J.low.hp J.low.sizePos high.hp high.sizePos hv
    eq jet.result A D.extra j t J.roster.rows
  let scratch := encodeArrays scalarPayload (combineArrays (uGates high.hp high.words) head suffix lifted.result.val)
  let resumed := resumeUV high.hp saved
    (addM high.hp (mulM high.hp weight ⟨lifted.result,coeff.steps+lifted.steps+4⟩)
      (sumM high.hp step ((List.range J.window).drop (j+1))))
  let run := emittedCentreMeter D hq hp hv hf child
  let lowBits := ell*(J.low.words.length*registerPrecision S c (D.tag x))
  let highBits := ell*(high.words.length*(c.prec+D.extra))
  run x=⟨resumed.result,J.tape.steps+jet.steps+resumed.steps+
    tapeFee J.low.words.length ell (registerPrecision S c (D.tag x)) J.window+4⟩ ∧
  ∃ pre post,actualEmittedCentreRows D=pre++x::post ∧
    D.highRun hq hp hv hf child=
      resumeUV high.hp (pre.map run) (addM high.hp (run x) (sumM high.hp run post)) ∧
    resident+rawStockBits D.stock+(scalarTermsPayload (pre.map run)).length+
      (kept++(operands++scratch)).length≤
      roof+rawStockBits D.stock+D.stock.rows.length*highBits+
      (J.window*highBits+J.window*lowBits+
        ((lowBits+(highBits+highBits))+(10*ell)*(high.words.length*(c.prec+D.extra))))

theorem actual_emitted_centre_weighted_term_keeps_its_multiply_arrays
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (D : Schedule sel (readyAtPath T p a) T.bank q) (x : D.EmitRow)
    (hq : 0<q) (child : ActiveChild (sel:=sel) (d:=readyAtPath T p a) T.bank)
    (j : ℕ) (hj : j<(D.fetch x).window)
    (left : List (UBlock (D.high (reachable_positive T p.reached)).words))
    (head : UBlock (D.high (reachable_positive T p.reached)).words)
    (suffix : List (UBlock (D.high (reachable_positive T p.reached)).words))
    (cut : let high := D.high (reachable_positive T p.reached)
      (rawWeight high.hp high.sizePos T.vPositive ((S).levelBits c.depth) D.extra j
        (D.tag x).val (D.fetch x).roster.rows).result.val=left++head::suffix)
    (resident roof : ℕ) (fits : resident≤roof) :
    NamedRawWeightedTermMultiply p a D x hq child j head suffix resident roof := by
  let hp := reachable_positive T p.reached
  let hv := T.vPositive
  let J := D.fetch x
  let high := D.high hp
  let t := (D.tag x).val
  let A := (S).levelBits c.depth
  let jet := J.centreJet hq hv (child (D.tag x))
  let eq := (J.low.natDegree hf).trans (high.natDegree hf).symm
  let run := emittedCentreMeter D hq hp hv hf child
  obtain ⟨resumes,cap⟩ := actual_hermite_fold_and_multiply_have_one_phase_bound
    J.low.hp J.low.sizePos high.hp high.sizePos hv eq jet.result A D.extra j t J.roster.rows
    hj left head suffix cut
  obtain ⟨pre,post,ordered,fold⟩ :=
    selected_stock_row_is_an_actual_sweep_operand D hq hp hv hf child x
  have len : (actualEmittedCentreRows D).length=D.stock.rows.length := by
    simp only [actualEmittedCentreRows,List.length_pmap]
  have pref : pre.length≤D.stock.rows.length := by
    rw [ordered,List.length_append] at len
    exact (Nat.le_add_right _ _).trans_eq len
  have earlier : (scalarTermsPayload (pre.map run)).length≤
      D.stock.rows.length*(ell*(high.words.length*(c.prec+D.extra))) := by
    rw [scalar_terms_payload_exact,List.length_map]
    exact Nat.mul_le_mul_right _ pref
  refine ⟨?_,pre,post,ordered,fold,Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add_right fits _) earlier) cap⟩
  have literal := emitted_row_consumes_its_literal_jet_roster_margin_and_frames D hq hp hv hf child x
  let wrap (m : Meter (Block high ell)) : Meter (Block high ell) :=
    ⟨m.result,J.tape.steps+jet.steps+m.steps+
      tapeFee J.low.words.length ell (registerPrecision S c (D.tag x)) J.window+4⟩
  exact literal.trans (congrArg wrap resumes)

theorem actual_raw_path_retains_weighted_term_multiply_with_named_resident
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (shared carry roof : ℕ)
    (fit : recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p≤roof) :
    let D := (rawScheduleAt M F chart E B own p a).result
    let child := rawReaderAt M F chart (retireSavedDirectory tails) B p a
    ∀ (x : D.EmitRow) (j : ℕ) (_hj : j<(D.fetch x).window)
      (left : List (UBlock (D.high (reachable_positive T p.reached)).words))
      (head : UBlock (D.high (reachable_positive T p.reached)).words)
      (suffix : List (UBlock (D.high (reachable_positive T p.reached)).words)),
      (let high := D.high (reachable_positive T p.reached)
       (rawWeight high.hp high.sizePos T.vPositive ((S).levelBits c.depth) D.extra j
          (D.tag x).val (D.fetch x).roster.rows).result.val=left++head::suffix) →
      NamedRawWeightedTermMultiply p a D x M.modeWidth child j head suffix
        (recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p) roof := by
  intro D child x j hj left head suffix cut
  exact actual_emitted_centre_weighted_term_keeps_its_multiply_arrays p a D x M.modeWidth child
    j hj left head suffix cut _ _ fit

#print axioms actual_emitted_centre_weighted_term_keeps_its_multiply_arrays
#print axioms actual_raw_path_retains_weighted_term_multiply_with_named_resident
end
end J6R75RawPeak
