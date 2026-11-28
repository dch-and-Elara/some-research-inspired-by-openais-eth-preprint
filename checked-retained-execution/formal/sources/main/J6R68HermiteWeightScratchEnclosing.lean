import J6R68HermiteWeightScratchActual
import J6R50NonModeScratchRetained

/-! Bind the newly measured inverse cut to the same R50 retained
Hermite term. This proof counts only the operands while rawWeight is
still computing the inverse, not the later R70 final multiplication. -/
namespace J6R68.HermiteWeightScratch
open scoped Polynomial
open A1R10 A1R11 A1R12 AOracleMachineTime J6R23ScheduleWeight J6R22Active
open J6R21Leaf J6R50NonModeScratch J6R49NonModeStack J6R19Retained
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 7600000

variable {p q ell J : ℕ} {old : List (Word p)} {high : List (Word q)}

theorem same_hermite_term_holds_actual_jet_and_all_named_inverse_operands
    (hp : 0<p) (he : 0<old.length) (hq : 0<q) (hh : 0<high.length) (hv : 0<ell)
    (shape : old.length=high.length) (jet : JetTape old ell J)
    (a B j : ℕ) (t : ℤ) (xs : List (ℤ×ℕ)) (hj : j<J)
    (u n : ℕ) (turn : u+1+n=q)
    (pre : List (UBlock high)) (h : UBlock high) (tail : List (UBlock high))
    (cut : (inverseDelta hq hh hv
      (stored (nativeWeightFold hq hh hv a t j xs .den).result.odd)).result.val=pre++h::tail) :
    let step := fun i => termM hp he hq hh hv shape jet a B i t xs
    let saved := ((List.range J).take j).map step
    let kept := scalarTermsPayload saved++jetPayload jet
    let coefficient := jetCoeffM hp he jet j
    let resized := resizeUV shape coefficient.result
    let N := nativeWeightFold hq hh hv a t j xs .num
    let D := nativeWeightFold hq hh hv a t j xs .den
    let x := stored D.result.odd
    let y := inverseDelta hq hh hv x
    let acc := uvCorrection hq hh hv y.result u
    let rest := resumeCorrection hq hh hv y.result n (correctionReturn hq hh hv y.result acc)
    let next := finishWeightFromOddInverse hq hh hv a B j N D
      ⟨rest.result,x.steps+(y.steps+rest.steps+uvWidth high.length ell q+4)+2⟩
    let inverseWords := weightBlocks [N.result.odd,x.result,y.result,acc.result]
    let arrays := encodeArrays scalarPayload (combineArrays (uGates hq high) h tail acc.result.val)
    sumM hq step (List.range J)=
      resumeUV hq saved (addM hq (mulM hq next
        ⟨resized.result,coefficient.steps+resized.steps+4⟩)
        (sumM hq step ((List.range J).drop (j+1)))) ∧
      ((kept++(leafPayload coefficient.result++leafPayload resized.result))++
        (inverseWords++arrays)).length≤
        (j*(ell*(high.length*q))+J*(ell*(old.length*p))+
          (ell*(old.length*p)+ell*(high.length*q)))+
        (4*(ell*(high.length*q))+(10*ell)*(high.length*q)) := by
  let step := fun i=>termM hp he hq hh hv shape jet a B i t xs
  let saved := ((List.range J).take j).map step
  let kept := scalarTermsPayload saved++jetPayload jet
  let coefficient := jetCoeffM hp he jet j
  let resized := resizeUV shape coefficient.result
  let N := nativeWeightFold hq hh hv a t j xs .num
  let D := nativeWeightFold hq hh hv a t j xs .den
  let x := stored D.result.odd
  let y := inverseDelta hq hh hv x
  let acc := uvCorrection hq hh hv y.result u
  let rest := resumeCorrection hq hh hv y.result n (correctionReturn hq hh hv y.result acc)
  let next := finishWeightFromOddInverse hq hh hv a B j N D
    ⟨rest.result,x.steps+(y.steps+rest.steps+uvWidth high.length ell q+4)+2⟩
  let inverseWords := weightBlocks [N.result.odd,x.result,y.result,acc.result]
  let arrays := encodeArrays scalarPayload (combineArrays (uGates hq high) h tail acc.result.val)
  have outer := actual_hermite_retained_words hp he hq hh hv shape jet a B j t xs hj.le
  have inner := actual_raw_weight_inverse_uses_its_true_folds_and_horner_scratch hq hh hv
    a B j t xs u n turn pre h tail cut
  have now : step j=mulM hq next ⟨resized.result,coefficient.steps+resized.steps+4⟩ := by
    change mulM hq (rawWeight hq hh hv a B j t xs)
      ⟨resized.result,coefficient.steps+resized.steps+4⟩=_
    exact congrArg (fun w=>mulM hq w ⟨resized.result,coefficient.steps+resized.steps+4⟩) inner.1
  constructor
  · change sumM hq step (List.range J)=resumeUV hq saved (addM hq _ _)
    have current : (List.range J).drop j=j::(List.range J).drop (j+1) := by
      have point : j < (List.range J).length := by simpa only [List.length_range] using hj
      rw [List.drop_eq_getElem_cons point,List.getElem_range]
    calc
      _=resumeUV hq saved (sumM hq step ((List.range J).drop j)) := outer.1
      _=resumeUV hq saved (addM hq (step j) (sumM hq step ((List.range J).drop (j+1)))) := by
        rw [current]
        rfl
      _=_ := congrArg (fun m=>resumeUV hq saved (addM hq m (sumM hq step ((List.range J).drop (j+1))))) now
  · change ((kept++(leafPayload coefficient.result++leafPayload resized.result))++
        (inverseWords++arrays)).length≤_
    have keep : kept.length=j*(ell*(high.length*q))+J*(ell*(old.length*p)) := outer.2
    have total : (kept++(leafPayload coefficient.result++leafPayload resized.result)).length=
        j*(ell*(high.length*q))+J*(ell*(old.length*p))+
          (ell*(old.length*p)+ell*(high.length*q)) := by
      calc
        _=kept.length+(leafPayload coefficient.result++leafPayload resized.result).length :=
          List.length_append
        _=_ := by rw [keep,List.length_append,leaf_payload_width,leaf_payload_width]
    rw [List.length_append,total]
    exact Nat.add_le_add_left inner.2.2 _

#print axioms same_hermite_term_holds_actual_jet_and_all_named_inverse_operands
end J6R68.HermiteWeightScratch
