import J6R49NonModeStackInterp
import J6R24MeteredRecursionFrame

/-! The two halves of the suspension attach to the actual center
interpreter: the weighted probe fold resumes, and then the unchanged
quotient computation runs. This is an observer of the original
center, not a new evaluator or an arithmetic workspace model. -/
namespace J6R49NonModeStack
open scoped Polynomial
open A1R10 AOracleMachineTime J6R21Leaf J6R22Active J6R24MeteredRecursion
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

variable {p ell k n : ℕ} {fw : List (A1R10.Word p)}
variable (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)

def resumedInterpolation (saved : List (J fw ell k)) (b : J fw ell k)
    (received : Meter (UVBlock fw ell)) (later : J fw ell k) (n : ℕ) : J fw ell k :=
  let ready := unwind hp he saved (joinJet hp he (finishTerm hp he hk b received) later)
  ⟨ready.result,ready.steps+4*(n+1)^2+4⟩

def resumeCenter (saved : List (J fw ell k)) (b : J fw ell k)
    (received : Meter (UVBlock fw ell)) (later normal : J fw ell k) (n : ℕ) : J fw ell k :=
  let val := resumedInterpolation hp he hk saved b received later n
  let q := divideJet hp he hv hk normal.result val.result
  ⟨q.result,normal.steps+val.steps+q.steps+4⟩

/-- Same original meter, including the unchanged quotient after the
interpolator has resumed. No length claim is made for quotient scratch. -/
theorem full_center_pauses_at_literal_probe
    (node sample : Fin n→Meter (UVBlock fw ell)) (normal : J fw ell k) (i : Fin n) :
    let saved := completedTerms hp he hv hk node sample i
    let b := basisM hp he hv hk node i
    let later := paidJetSum hp he (interpTerm hp he hv hk node sample) ((probeOrder n).drop (i.val+1))
    fullCenterM hp he hv hk node sample normal=
      resumeCenter hp he hv hk saved b (sample i) later normal n := by
  exact congrArg (fun v : J fw ell k=>
     let q := divideJet hp he hv hk normal.result v.result
     (⟨q.result,normal.steps+v.steps+q.steps+4⟩ : J fw ell k))
    (interp_prefix_pause_exact hp he hv hk node sample i)

/-- Width on the actual monic finite receiver. The size caps from
source scheduling can be inserted here without treating the jet order
as the probe count or the field degree as an unknown word length. -/
theorem native_frame_paused_jet_payload {f : ℤ[X]} (F : Frame f p)
    (hf : f.Monic) (hv : 0<ell) (hk : 0<k)
    (node sample : Fin n→Meter (Block F ell))
    (normal : J F.words ell k) (i : Fin n) :
    let bits := pausedJetFields F.hp F.sizePos hv hk node sample i normal
    bits.length=(i.val+2)*(k*(ell*(f.natDegree*p))) ∧
      bits.length≤(n+1)*(k*(ell*(f.natDegree*p))) := by
  have h := paused_jet_fields_exact F.hp F.sizePos hv hk node sample i normal
  have b := paused_jet_fields_bound F.hp F.sizePos hv hk node sample i normal
  rw [F.natDegree hf] at h b
  exact ⟨h,b⟩

#print axioms full_center_pauses_at_literal_probe
#print axioms native_frame_paused_jet_payload
end J6R49NonModeStack
