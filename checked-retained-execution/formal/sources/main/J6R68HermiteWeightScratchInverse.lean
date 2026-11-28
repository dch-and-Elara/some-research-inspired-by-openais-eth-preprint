import A1R12Combine
import J6R50NonModeScratchNative

/-! The actual finite odd-inverse kernel, with exact fixed-width
operands at a genuine Horner recurrence cut. The named layout uses
one copy of the shared correction argument, not p copies. Internal
U arithmetic, Nat clock digits, and allocator storage are not counted. -/
namespace J6R68.HermiteWeightScratch
open A1R10 A1R11 A1R12 AOracleMachineTime
open J6R21Leaf J6R50NonModeScratch
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 4700000

variable {p ell : ℕ} {fw : List (Word p)}

def weightBlocks (xs : List (UVBlock fw ell)) : List Bool :=
  xs.flatMap leafPayload

theorem weight_block_payload_exact (xs : List (UVBlock fw ell)) :
    (weightBlocks xs).length=xs.length*(ell*(fw.length*p)) := by
  unfold weightBlocks
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,leaf_payload_width,ih,
      Nat.add_mul,Nat.one_mul,Nat.add_comm]

def correctionReturn (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : UVBlock fw ell) (inner : Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  let prod := uvMul hp x inner.result
  let added := uvAdd hp (uvOne hp he hv) prod.result
  ⟨added.result,inner.steps+prod.steps+added.steps+uvWidth fw.length ell p+4⟩

def resumeCorrection (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : UVBlock fw ell) : ℕ→Meter (UVBlock fw ell)→Meter (UVBlock fw ell)
  | 0,later => later
  | n+1,later => correctionReturn hp he hv x (resumeCorrection hp he hv x n later)

theorem literal_horner_resume_is_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : UVBlock fw ell) (k n : ℕ) :
    uvCorrection hp he hv x (k+n)=
      resumeCorrection hp he hv x n (uvCorrection hp he hv x k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (correctionReturn hp he hv x) ih

def inverseDelta (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  uvSub hp he (uvOne hp he hv) x.result

theorem actual_invM_reaches_the_exact_horner_return
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (x : Meter (UVBlock fw ell)) (k n : ℕ) (split : k+1+n=p) :
    let y := inverseDelta hp he hv x
    let inside := uvCorrection hp he hv y.result k
    let later := resumeCorrection hp he hv y.result n (correctionReturn hp he hv y.result inside)
    invM hp he hv x=
      ⟨later.result,x.steps+(y.steps+later.steps+uvWidth fw.length ell p+4)+2⟩ := by
  let y := inverseDelta hp he hv x
  let inside := uvCorrection hp he hv y.result k
  let later := resumeCorrection hp he hv y.result n (correctionReturn hp he hv y.result inside)
  have eq : uvCorrection hp he hv y.result p=later := by
    calc
      _=uvCorrection hp he hv y.result (k+1+n) :=
        congrArg (uvCorrection hp he hv y.result) split.symm
      _=resumeCorrection hp he hv y.result n (uvCorrection hp he hv y.result (k+1)) :=
        literal_horner_resume_is_exact hp he hv y.result (k+1) n
      _=later := rfl
  change (⟨(uvCorrection hp he hv y.result p).result,
    x.steps+(y.steps+(uvCorrection hp he hv y.result p).steps+uvWidth fw.length ell p+4)+2⟩ :
    Meter (UVBlock fw ell))=_
  rw [eq]

theorem inverse_horner_uses_actual_multiply_operands_and_arrays
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (retained : UVBlock fw ell) (x : Meter (UVBlock fw ell)) (k : ℕ)
    (pre : List (UBlock fw)) (h : UBlock fw) (tail : List (UBlock fw))
    (cut : (inverseDelta hp he hv x).result.val=pre++h::tail) :
    let y := (inverseDelta hp he hv x).result
    let acc := (uvCorrection hp he hv y k).result
    let operands := weightBlocks [retained,x.result,y,acc]
    let arrays := encodeArrays scalarPayload (combineArrays (uGates hp fw) h tail acc.val)
    operands.length=4*(ell*(fw.length*p)) ∧
      (operands++arrays).length≤4*(ell*(fw.length*p))+(10*ell)*(fw.length*p) := by
  dsimp only
  rw [List.length_append,weight_block_payload_exact]
  have array := native_v_convolution_scratch hp (inverseDelta hp he hv x).result
    (uvCorrection hp he hv (inverseDelta hp he hv x).result k).result pre h tail cut
  exact ⟨rfl,Nat.add_le_add_left array _⟩

theorem inverse_horner_add_boundary_has_native_block_widths
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (retained : UVBlock fw ell) (x : Meter (UVBlock fw ell)) (k : ℕ) :
    let y := (inverseDelta hp he hv x).result
    let acc := uvCorrection hp he hv y k
    let prod := uvMul hp y acc.result
    let next := correctionReturn hp he hv y acc
    (weightBlocks [retained,x.result,y,acc.result,prod.result,uvOne hp he hv,next.result]).length=
      7*(ell*(fw.length*p)) := by
  dsimp only
  exact weight_block_payload_exact _

#print axioms weight_block_payload_exact
#print axioms literal_horner_resume_is_exact
#print axioms actual_invM_reaches_the_exact_horner_return
#print axioms inverse_horner_uses_actual_multiply_operands_and_arrays
#print axioms inverse_horner_add_boundary_has_native_block_widths
end J6R68.HermiteWeightScratch
