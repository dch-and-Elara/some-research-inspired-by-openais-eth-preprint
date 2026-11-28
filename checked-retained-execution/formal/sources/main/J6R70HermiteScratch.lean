import J6R50NonModeScratchRetained
import J6R50NonModeScratchNative

/-! Scratch fields at the actual multiply in a source Hermite term.
This measures the coefficient copy, its resized operand and the actual
modular weight while the original jet and earlier weighted heads are live.
The observer does not allocate the concatenated tape in the running machine.
The internal rawWeight/inversion/resize scratch is a separate phase. -/
namespace J6R70HermiteScratch
open A1R10 A1R12 AOracleMachineTime J6R21Leaf J6R22Active J6R23ScheduleWeight
open J6R19Retained J6R50NonModeScratch J6R49NonModeStack
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000

variable {p q ell k : Nat}
variable {old : List (Word p)} {high : List (Word q)}

def multiplyOperands (hp : 0<p) (he : 0<old.length)
    (hq : 0<q) (hh : 0<high.length) (hv : 0<ell)
    (eq : old.length=high.length) (jet : JetTape old ell k)
    (a B j : Nat) (t : Int) (roster : List (Int × Nat)) : List Bool :=
  let x := jetCoeffM hp he jet j
  let y := resizeUV eq x.result
  let w := rawWeight hq hh hv a B j t roster
  leafPayload x.result ++ (leafPayload y.result ++ leafPayload w.result)

theorem literal_multiply_operands_width (hp : 0<p) (he : 0<old.length)
    (hq : 0<q) (hh : 0<high.length) (hv : 0<ell) (eq : old.length=high.length)
    (jet : JetTape old ell k) (a B j : Nat) (t : Int) (roster : List (Int × Nat)) :
    (multiplyOperands hp he hq hh hv eq jet a B j t roster).length =
      ell*(old.length*p) + (ell*(high.length*q) + ell*(high.length*q)) := by
  simp only [multiplyOperands, List.length_append, leaf_payload_width]

theorem actual_hermite_fold_multiply_selected_peak (hp : 0<p) (he : 0<old.length)
    (hq : 0<q) (hh : 0<high.length) (hv : 0<ell) (eq : old.length=high.length)
    (jet : JetTape old ell k) (a B j : Nat) (t : Int) (roster : List (Int × Nat))
    (hj : j<k) :
    let step := fun x => termM hp he hq hh hv eq jet a B x t roster
    let saved := ((List.range k).take j).map step
    let rest := sumM hq step ((List.range k).drop j)
    let kept := scalarTermsPayload saved ++ jetPayload jet
    let operands := multiplyOperands hp he hq hh hv eq jet a B j t roster
    sumM hq step (List.range k)=resumeUV hq saved rest ∧
      (kept ++ operands).length ≤
        k*(ell*(high.length*q)) + k*(ell*(old.length*p)) +
          (ell*(old.length*p) + (ell*(high.length*q) + ell*(high.length*q))) := by
  have h := actual_hermite_retained_words hp he hq hh hv eq jet a B j t roster hj.le
  dsimp only at h ⊢
  refine ⟨h.1, ?_⟩
  rw [List.length_append, h.2, literal_multiply_operands_width]
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hj.le) _) _

theorem actual_hermite_multiply_phase (hp : 0<p) (he : 0<old.length)
    (hq : 0<q) (hh : 0<high.length) (hv : 0<ell)
    (eq : old.length=high.length) (jet : JetTape old ell k)
    (a B j : Nat) (t : Int) (roster : List (Int × Nat))
    (pref : List (UBlock high)) (head : UBlock high) (suffix : List (UBlock high))
    (cut : (rawWeight hq hh hv a B j t roster).result.val=pref++head::suffix) :
    let x := jetCoeffM hp he jet j
    let y := resizeUV eq x.result
    let weight := rawWeight hq hh hv a B j t roster
    let scratch := encodeArrays scalarPayload (combineArrays (uGates hq high) head suffix y.result.val)
    termM hp he hq hh hv eq jet a B j t roster =
      mulM hq weight ⟨y.result,x.steps+y.steps+4⟩ ∧
      (multiplyOperands hp he hq hh hv eq jet a B j t roster ++ scratch).length ≤
        ell*(old.length*p) + (ell*(high.length*q) + ell*(high.length*q)) +
          (10*ell)*(high.length*q) := by
  dsimp only
  refine ⟨rfl, ?_⟩
  rw [List.length_append, literal_multiply_operands_width]
  exact Nat.add_le_add_left
    (native_v_convolution_scratch hq (rawWeight hq hh hv a B j t roster).result
      (resizeUV eq (jetCoeffM hp he jet j).result).result pref head suffix cut) _
theorem actual_hermite_fold_and_multiply_have_one_phase_bound
    (hp : 0<p) (he : 0<old.length) (hq : 0<q) (hh : 0<high.length) (hv : 0<ell)
    (eq : old.length=high.length) (jet : JetTape old ell k)
    (a B j : Nat) (t : Int) (roster : List (Int × Nat)) (hj : j<k)
    (pref : List (UBlock high)) (head : UBlock high) (suffix : List (UBlock high))
    (cut : (rawWeight hq hh hv a B j t roster).result.val=pref++head::suffix) :
    let step := fun i => termM hp he hq hh hv eq jet a B i t roster
    let saved := ((List.range k).take j).map step
    let kept := scalarTermsPayload saved ++ jetPayload jet
    let x := jetCoeffM hp he jet j
    let y := resizeUV eq x.result
    let w := rawWeight hq hh hv a B j t roster
    let scratch := encodeArrays scalarPayload (combineArrays (uGates hq high) head suffix y.result.val)
    let operands := multiplyOperands hp he hq hh hv eq jet a B j t roster
    sumM hq step (List.range k) =
      resumeUV hq saved (addM hq (mulM hq w ⟨y.result,x.steps+y.steps+4⟩)
        (sumM hq step ((List.range k).drop (j+1)))) ∧
      (kept ++ (operands ++ scratch)).length ≤
        k*(ell*(high.length*q)) + k*(ell*(old.length*p)) +
          (ell*(old.length*p) + (ell*(high.length*q) + ell*(high.length*q)) +
            (10*ell)*(high.length*q)) := by
  have h := actual_hermite_retained_words hp he hq hh hv eq jet a B j t roster hj.le
  have phase := actual_hermite_multiply_phase hp he hq hh hv eq jet a B j t roster pref head suffix cut
  dsimp only at h phase ⊢
  constructor
  · rw [h.1]
    have hj' : j < (List.range k).length := by simpa using hj
    have next : (List.range k).drop j = j :: (List.range k).drop (j+1) := by
      rw [List.drop_eq_getElem_cons hj',List.getElem_range]
    rw [next, sumM, phase.1]
  · rw [List.length_append,h.2]
    exact Nat.add_le_add
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hj.le) _) phase.2
#print axioms actual_hermite_fold_and_multiply_have_one_phase_bound
#print axioms actual_hermite_multiply_phase
#print axioms literal_multiply_operands_width
#print axioms actual_hermite_fold_multiply_selected_peak
end J6R70HermiteScratch
