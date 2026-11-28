import J6R49NonModeStackPayload
import J6R23ScheduleWeightTerm

/-! Retained outputs of the original scalar right fold, including the
actual Hermite terms applied to the same checked quotient jet. -/
namespace J6R50NonModeScratch
open A1R10 A1R12 AOracleMachineTime J6R21Leaf J6R22Active J6R23ScheduleWeight
open J6R49NonModeStack (jetPayload jet_payload_length)
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

variable {p q ell k : ℕ}
variable {old : List (A1R10.Word p)} {high : List (A1R10.Word q)}

def resumeUV (hq : 0<q) (saved : List (Meter (UVBlock high ell)))
    (later : Meter (UVBlock high ell)) :=
  saved.foldr (addM hq) later

theorem scalar_sum_retains_actual_heads {A : Type*} (hq : 0<q)
    (step : A→Meter (UVBlock high ell)) (before after : List A) :
    sumM hq step (before++after)=resumeUV hq (before.map step) (sumM hq step after) := by
  induction before with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append,sumM,resumeUV,List.map_cons,List.foldr_cons,ih]

def scalarTermsPayload (saved : List (Meter (UVBlock high ell))) : List Bool :=
  saved.flatMap (fun x=>leafPayload x.result)

theorem scalar_terms_payload_exact (saved : List (Meter (UVBlock high ell))) :
    (scalarTermsPayload saved).length=saved.length*(ell*(high.length*q)) := by
  induction saved with
  | nil => simp [scalarTermsPayload]
  | cons x xs ih =>
    change (leafPayload x.result++scalarTermsPayload xs).length=
      (xs.length+1)*(ell*(high.length*q))
    rw [List.length_append,leaf_payload_width,ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]

/-- Weighted high-register terms already computed before evaluating term
j, together with the real unchanged low quotient jet. The receipt code
does not allocate the flattened observer during the original run. -/
theorem actual_hermite_retained_words (hp : 0<p) (he : 0<old.length)
    (hq : 0<q) (hh : 0<high.length) (hv : 0<ell) (eq : old.length=high.length)
    (jet : JetTape old ell k) (a B j : ℕ) (t : ℤ) (roster : List (ℤ×ℕ)) (hj : j≤k) :
    let step := fun s=>termM hp he hq hh hv eq jet a B s t roster
    let saved := ((List.range k).take j).map step
    let rest := sumM hq step ((List.range k).drop j)
    sumM hq step (List.range k)=resumeUV hq saved rest ∧
      (scalarTermsPayload saved++jetPayload jet).length=
        j*(ell*(high.length*q))+k*(ell*(old.length*p)) := by
  dsimp only
  constructor
  · exact (congrArg (sumM hq (fun s=>termM hp he hq hh hv eq jet a B s t roster))
      (List.take_append_drop j (List.range k)).symm).trans
      (scalar_sum_retains_actual_heads hq _ _ _)
  · simp only [List.length_append,scalar_terms_payload_exact,jet_payload_length,
      List.length_map,List.length_take,List.length_range,min_eq_left hj]

theorem meter_zero_step_result_has_no_uniform_width :
    ¬∃ w : ℕ,∀ m : Meter (List Bool),m.steps=0→m.result.length≤w := by
  rintro ⟨w,h⟩
  have impossible := h ⟨List.replicate (w+1) false,0⟩ rfl
  have hw : w+1≤w := by simpa only [List.length_replicate] using impossible
  omega

#print axioms scalar_sum_retains_actual_heads
#print axioms scalar_terms_payload_exact
#print axioms actual_hermite_retained_words
#print axioms meter_zero_step_result_has_no_uniform_width
end J6R50NonModeScratch
