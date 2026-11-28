import J6R75RawPeakCarry
import J6R68HermiteWeightScratchRawInverse

/-! Keep the very same raw suspended ancestor fields across the actual
child's publication, physical mount, and return. The local cuts are
different phases, with maximum rather than additive scratch. -/
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
set_option maxHeartbeats 4900000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew width : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)

theorem true_raw_hermite_inverse_keeps_the_same_ancestor_carry
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (shared pageBound fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit M pageBound) (sizes : EntryWidths M fixed addr)
    (boot : BootBodyWidth M seed) (owners : OwnerWidth M owner)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (carry : ℕ) (anc : ActualRawAncestorStack M F chart E B own tails p carry)
    (D : Schedule sel (readyAtPath T p a) T.bank q)
    (child : ActiveChild (sel:=sel) (d:=readyAtPath T p a) T.bank)
    (issued : D=(rawScheduleAt M F chart E B own p a).result)
    (callback : child=rawReaderAt M F chart (retireSavedDirectory tails) B p a)
    (x : D.EmitRow)
    (j : ℕ) (hj : j<(D.fetch x).window) (u turns : ℕ) (turn : u+1+turns=c.prec+D.extra)
    (prior : List (UBlock (D.high (reachable_positive T p.reached)).words))
    (head : UBlock (D.high (reachable_positive T p.reached)).words)
    (tail : List (UBlock (D.high (reachable_positive T p.reached)).words))
    (cut : (stockInverseDelta D (reachable_positive T p.reached) T.vPositive x j).result.val=prior++head::tail) :
    let A := (S).levelBits c.depth
    let hq := M.modeWidth
    let hp := reachable_positive T p.reached
    let hv := T.vPositive
    let run := emittedCentreMeter D hq hp hv hf child
    let J := D.fetch x
    let high := D.high hp
    let jet := J.centreJet hq hv (child (D.tag x))
    let equal := (J.low.natDegree hf).trans (high.natDegree hf).symm
    let step := fun i=>J.centreTerm hv hf high D.extra jet.result i
    let saved := ((List.range J.window).take j).map step
    let kept := scalarTermsPayload saved++jetPayload jet.result
    let coefficient := jetCoeffM J.low.hp J.low.sizePos jet.result j
    let resized := resizeUV equal coefficient.result
    let N := nativeWeightFold high.hp high.sizePos hv A (D.tag x).val j J.roster.rows .num
    let Den := nativeWeightFold high.hp high.sizePos hv A (D.tag x).val j J.roster.rows .den
    let xD := stored Den.result.odd
    let y := stockInverseDelta D hp hv x j
    let acc := uvCorrection high.hp high.sizePos hv y.result u
    let finished := resumeCorrection high.hp high.sizePos hv y.result turns
      (correctionReturn high.hp high.sizePos hv y.result acc)
    let next := finishWeightFromOddInverse high.hp high.sizePos hv A D.extra j N Den
      ⟨finished.result,xD.steps+(y.steps+finished.steps+uvWidth high.words.length ell (c.prec+D.extra)+4)+2⟩
    let resumed := resumeUV high.hp saved (addM high.hp (mulM high.hp next
      ⟨resized.result,coefficient.steps+resized.steps+4⟩)
      (sumM high.hp step ((List.range J.window).drop (j+1))))
    let inverseWords := weightBlocks [N.result.odd,xD.result,y.result,acc.result]
    let arrays := encodeArrays scalarPayload (combineArrays (uGates high.hp high.words) head tail acc.result.val)
    let lowBits := ell*(J.low.words.length*registerPrecision S c (D.tag x))
    let highBits := ell*(high.words.length*(c.prec+D.extra))
    let localBits := ((kept++(leafPayload coefficient.result++leafPayload resized.result))++
      (inverseWords++arrays)).length
    let allowance := (j*highBits+J.window*lowBits+(lowBits+highBits))+
        (4*highBits+(10*ell)*(high.words.length*(c.prec+D.extra)))
    D.stock=(rawScheduleAt M F chart E B own p a).result.stock ∧
    child=rawReaderAt M F chart (retireSavedDirectory tails) B p a ∧
    run x=⟨resumed.result,J.tape.steps+jet.steps+resumed.steps+
        tapeFee J.low.words.length ell (registerPrecision S c (D.tag x)) J.window+4⟩ ∧
    ∃ pre post,actualEmittedCentreRows D=pre++x::post ∧
      D.highRun hq hp hv hf child=
        resumeUV high.hp (pre.map run) (addM high.hp (run x) (sumM high.hp run post)) ∧
      recursiveResidentBits shared M B p carry+rawStockBits D.stock+
        (scalarTermsPayload (pre.map run)).length+localBits≤
        rawCarrierRoof shared B r pageBound fixed addr seed owner s C q+
          rawStockBits D.stock+D.stock.rows.length*highBits+allowance := by
  let hp := reachable_positive T p.reached
  let run := emittedCentreMeter D M.modeWidth hp T.vPositive hf child
  obtain ⟨pre,post,rows,fold⟩ :=
    selected_stock_row_is_an_actual_sweep_operand D M.modeWidth hp T.vPositive hf child x
  obtain ⟨inverse,fit⟩ := actual_emitted_row_has_one_literal_inverse_phase D M.modeWidth
    hp T.vPositive hf child x j hj u turns turn prior head tail cut
  have carryFit := raw_ancestor_and_same_physical_carrier_fit_together M F chart E B own tails
    shared pageBound fixed addr seed owner pageFit sizes boot owners p carry anc
  refine ⟨congrArg Schedule.stock issued,callback,inverse,pre,post,rows,fold,?_⟩
  have order : (actualEmittedCentreRows D).length=D.stock.rows.length := by
    simp only [actualEmittedCentreRows,List.length_pmap]
  have preLen : pre.length≤D.stock.rows.length := by
    rw [rows,List.length_append] at order
    exact (Nat.le_add_right _ _).trans_eq order
  have preBits : (scalarTermsPayload (pre.map run)).length≤
      D.stock.rows.length*(ell*((D.high hp).words.length*(c.prec+D.extra))) := by
    rw [scalar_terms_payload_exact,List.length_map]
    exact Nat.mul_le_mul_right _ preLen
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right carryFit _) preBits) fit

#print axioms true_raw_hermite_inverse_keeps_the_same_ancestor_carry
end
end J6R75RawPeak
