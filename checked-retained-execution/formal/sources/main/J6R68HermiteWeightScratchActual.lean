import J6R68HermiteWeightScratchFold
import J6R23ScheduleWeightCompile

/-! Identify the actual R23 rawWeight receiver and its real two
tapered folds/odd inverse. These observations are before termM's
final multiply and neither count that phase twice nor alter it. -/
namespace J6R68.HermiteWeightScratch
open scoped Polynomial
open A1R10 A1R11 A1R12 AOracleMachineTime J6R23ScheduleWeight J6R22Active
open J6R21Leaf J6R50NonModeScratch
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 7100000

variable {p ell : ℕ} {fw : List (Word p)}

def rawWeightRows (b : Side) (t : ℤ) (j : ℕ) (xs : List (ℤ×ℕ)) : List (ℤ×ℕ) :=
  match b with
  | .num => xs++[(t,j)]
  | .den => xs

def nativeWeightFold (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a : ℕ) (t : ℤ) (j : ℕ) (xs : List (ℤ×ℕ)) (b : Side) : Meter (Part fw ell) :=
  foldParts hp he hv a t b (rawWeightRows b t j xs)

def earlierWeightBlocks (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a : ℕ) (t : ℤ) (j : ℕ) (xs : List (ℤ×ℕ)) : Side→List (UVBlock fw ell)
  | .num => []
  | .den => [(nativeWeightFold hp he hv a t j xs .num).result.odd]

def finishWeightFromOddInverse (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a B j : ℕ) (N D : Meter (Part fw ell)) (inv : Meter (UVBlock fw ell)) :
    Meter (UVBlock fw ell) :=
  let prod := mulM hp (stored N.result.odd) inv
  let shift := twoM hp he hv (B+N.result.two-(D.result.two+(a+1)*j))
  padCost (mulM hp shift prod) (N.steps+D.steps+8*(a+B+j+N.result.two+D.result.two+6)^2+10)

theorem actual_raw_weight_preparation_is_its_two_folds_and_invM
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a B j : ℕ) (t : ℤ) (xs : List (ℤ×ℕ)) :
    let N := nativeWeightFold hp he hv a t j xs .num
    let D := nativeWeightFold hp he hv a t j xs .den
    rawWeight hp he hv a B j t xs=
      finishWeightFromOddInverse hp he hv a B j N D (invM hp he hv (stored D.result.odd)) := rfl

theorem actual_raw_weight_fold_has_its_own_pending_blocks
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a j : ℕ) (t : ℤ) (xs : List (ℤ×ℕ)) (b : Side)
    (before after : List (ℤ×ℕ)) (q : ℤ×ℕ)
    (split : rawWeightRows b t j xs=before++q::after)
    (pre : List (UBlock fw)) (h : UBlock fw) (tail : List (UBlock fw))
    (cut : (weightFactor hp he hv a t b q).result.odd.val=pre++h::tail) :
    let saved := before.map (weightFactor hp he hv a t b)
    let l := weightFactor hp he hv a t b q
    let r := foldParts hp he hv a t b after
    let previous := earlierWeightBlocks hp he hv a t j xs b
    let operands := weightBlocks (previous++(saved.map (fun f=>f.result.odd))++[l.result.odd,r.result.odd])
    let arrays := encodeArrays scalarPayload (combineArrays (uGates hp fw) h tail r.result.odd.val)
    nativeWeightFold hp he hv a t j xs b=resumeParts hp a saved (foldPartReturn hp a l r) ∧
      operands.length=(previous.length+before.length+2)*(ell*(fw.length*p)) ∧
      (operands++arrays).length≤
        (previous.length+before.length+2)*(ell*(fw.length*p))+(10*ell)*(fw.length*p) := by
  dsimp only [nativeWeightFold]
  rw [split]
  exact actual_signed_fold_named_mul_cut hp he hv a t b before after q
    (earlierWeightBlocks hp he hv a t j xs b) pre h tail cut

theorem actual_raw_weight_inverse_uses_its_true_folds_and_horner_scratch
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a B j : ℕ) (t : ℤ) (xs : List (ℤ×ℕ))
    (k n : ℕ) (turn : k+1+n=p)
    (pre : List (UBlock fw)) (h : UBlock fw) (tail : List (UBlock fw))
    (cut : (inverseDelta hp he hv
      (stored (nativeWeightFold hp he hv a t j xs .den).result.odd)).result.val=pre++h::tail) :
    let N := nativeWeightFold hp he hv a t j xs .num
    let D := nativeWeightFold hp he hv a t j xs .den
    let x := stored D.result.odd
    let y := inverseDelta hp he hv x
    let acc := uvCorrection hp he hv y.result k
    let rest := resumeCorrection hp he hv y.result n (correctionReturn hp he hv y.result acc)
    let actualInv : Meter (UVBlock fw ell) :=
      ⟨rest.result,x.steps+(y.steps+rest.steps+uvWidth fw.length ell p+4)+2⟩
    let operands := weightBlocks [N.result.odd,x.result,y.result,acc.result]
    let arrays := encodeArrays scalarPayload (combineArrays (uGates hp fw) h tail acc.result.val)
    rawWeight hp he hv a B j t xs=finishWeightFromOddInverse hp he hv a B j N D actualInv ∧
      operands.length=4*(ell*(fw.length*p)) ∧
      (operands++arrays).length≤4*(ell*(fw.length*p))+(10*ell)*(fw.length*p) := by
  let N := nativeWeightFold hp he hv a t j xs .num
  let D := nativeWeightFold hp he hv a t j xs .den
  let x := stored D.result.odd
  dsimp only
  refine ⟨?_,inverse_horner_uses_actual_multiply_operands_and_arrays hp he hv N.result.odd
    x k pre h tail cut⟩
  rw [actual_raw_weight_preparation_is_its_two_folds_and_invM]
  exact congrArg (finishWeightFromOddInverse hp he hv a B j N D)
    (actual_invM_reaches_the_exact_horner_return hp he hv x k n turn)

theorem raw_weight_inverse_subtract_boundary_has_four_blocks
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a j : ℕ) (t : ℤ) (xs : List (ℤ×ℕ)) :
    let N := nativeWeightFold hp he hv a t j xs .num
    let D := nativeWeightFold hp he hv a t j xs .den
    let x := stored D.result.odd
    let z := uvOne hp he hv
    let y := inverseDelta hp he hv x
    (weightBlocks [N.result.odd,x.result,z,y.result]).length=4*(ell*(fw.length*p)) := by
  dsimp only
  exact weight_block_payload_exact _

#print axioms actual_raw_weight_preparation_is_its_two_folds_and_invM
#print axioms actual_raw_weight_fold_has_its_own_pending_blocks
#print axioms actual_raw_weight_inverse_uses_its_true_folds_and_horner_scratch
#print axioms raw_weight_inverse_subtract_boundary_has_four_blocks
end J6R68.HermiteWeightScratch
