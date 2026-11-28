import J6R68HermiteWeightScratchRawCore
import J6R68HermiteWeightScratchEnclosing

/-! Exactly instantiate the previously strict inverse cut at one
emitted-row receiver. The retained jet uses the raw sweep's real
child reader; no selected row is retrieved by Classical.proofRow. -/
namespace J6R68.HermiteWeightScratch
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active J6R19Retained
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R23ScheduleWeight J6R24MeteredRecursion J6R49DFS J6R21Leaf J6R49NonModeStack
open J6R50NonModeScratch J6R68ActiveInputs J6R68ActiveInputs.Sweep

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 14000000
set_option maxRecDepth 4300
set_option maxSynthPendingDepth 12

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s q : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f}
variable (D : Schedule sel d bank q)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)

def stockInverseDelta (hp : 0<c.prec) (hv : 0<ell) (x : D.EmitRow) (j : ℕ) :
    Meter (Block (D.high hp) ell) :=
  let J := D.fetch x
  let high := D.high hp
  let low := nativeWeightFold high.hp high.sizePos hv A (D.tag x).val j J.roster.rows .den
  inverseDelta high.hp high.sizePos hv (stored low.result.odd)

theorem actual_emitted_row_has_one_literal_inverse_phase
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) (x : D.EmitRow)
    (j : ℕ) (hj : j<(D.fetch x).window) (u n : ℕ) (turn : u+1+n=c.prec+D.extra)
    (pre : List (UBlock (D.high hp).words))
    (h : UBlock (D.high hp).words) (tail : List (UBlock (D.high hp).words))
    (cut : (stockInverseDelta D hp hv x j).result.val=pre++h::tail) :
    let J := D.fetch x
    let high := D.high hp
    let jet := J.centreJet hq hv (child (D.tag x))
    let eq := (J.low.natDegree hf).trans (high.natDegree hf).symm
    let step := fun i=>J.centreTerm hv hf high D.extra jet.result i
    let saved := ((List.range J.window).take j).map step
    let kept := scalarTermsPayload saved++jetPayload jet.result
    let coefficient := jetCoeffM J.low.hp J.low.sizePos jet.result j
    let resized := resizeUV eq coefficient.result
    let N := nativeWeightFold high.hp high.sizePos hv A (D.tag x).val j J.roster.rows .num
    let Den := nativeWeightFold high.hp high.sizePos hv A (D.tag x).val j J.roster.rows .den
    let xD := stored Den.result.odd
    let y := stockInverseDelta D hp hv x j
    let acc := uvCorrection high.hp high.sizePos hv y.result u
    let finished := resumeCorrection high.hp high.sizePos hv y.result n
      (correctionReturn high.hp high.sizePos hv y.result acc)
    let next := finishWeightFromOddInverse high.hp high.sizePos hv A D.extra j N Den
      ⟨finished.result,xD.steps+(y.steps+finished.steps+uvWidth high.words.length ell (c.prec+D.extra)+4)+2⟩
    let resumed := resumeUV high.hp saved (addM high.hp (mulM high.hp next
      ⟨resized.result,coefficient.steps+resized.steps+4⟩)
      (sumM high.hp step ((List.range J.window).drop (j+1))))
    let inverseWords := weightBlocks [N.result.odd,xD.result,y.result,acc.result]
    let arrays := encodeArrays scalarPayload (combineArrays (uGates high.hp high.words) h tail acc.result.val)
    let lowBits := ell*(J.low.words.length*registerPrecision S c (D.tag x))
    let highBits := ell*(high.words.length*(c.prec+D.extra))
    emittedCentreMeter D hq hp hv hf child x=
      ⟨resumed.result,J.tape.steps+jet.steps+resumed.steps+
        tapeFee J.low.words.length ell (registerPrecision S c (D.tag x)) J.window+4⟩ ∧
    ((kept++(leafPayload coefficient.result++leafPayload resized.result))++
      (inverseWords++arrays)).length ≤
      (j*highBits+J.window*lowBits+(lowBits+highBits))+
        (4*highBits+(10*ell)*(high.words.length*(c.prec+D.extra))) := by
  let J := D.fetch x
  let high := D.high hp
  let jet := J.centreJet hq hv (child (D.tag x))
  let equal := (J.low.natDegree hf).trans (high.natDegree hf).symm
  have h0 := same_hermite_term_holds_actual_jet_and_all_named_inverse_operands
    J.low.hp J.low.sizePos high.hp high.sizePos hv equal jet.result
    A D.extra j (D.tag x).val J.roster.rows hj u n turn pre h tail cut
  dsimp only
  refine ⟨?_,h0.2⟩
  rw [emitted_row_consumes_its_literal_jet_roster_margin_and_frames]
  dsimp only at h0
  rw [h0.1]
  rfl

#print axioms actual_emitted_row_has_one_literal_inverse_phase
end
end J6R68.HermiteWeightScratch
