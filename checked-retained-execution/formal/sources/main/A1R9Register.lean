import A1R9Scalar
import A1R9Multiplicity

/-! Scalar, arbitrary-mode A1 count from the metered bit witness.
The signed coefficient/crossing tape is supplied, and this theorem
prices the witness, not computing the tape or evaluating the count. -/

namespace A1R9
open scoped BigOperators
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open AOracleMachineTimeLocal AOracleMachineTimeZero
open AOracleSuccinct AOracleWitness AOracleThreshold

def scalarVerify {r c m delta p : ℕ} (br bc bm bq : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) (beta : Fin m →₀ ℕ)
    (w : Witness r c m) (d : Word p) : Meter Bool :=
  let a := runTensors (List.ofFn w.1) (L.rows.map (packTensor br))
  let b := runTensors (List.ofFn w.2.1) (L.cols.map (packTensor bc))
  let rows := runAllRows bm bc L w
  let count := checkMultiplicity bm bq beta (allocationWords bm w.2.2)
  let out := compareBits (encodeBits p d.val) rows.result.2
  ⟨a.result && b.result && rows.result.1 && count.result && out.result,
    a.steps+b.steps+rows.steps+count.steps+out.steps+8⟩

def witnessBudget {r c m delta p : ℕ} (br bc bm bq s : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) : ℕ :=
  L.rows.length*tensorBudget r delta br+L.cols.length*tensorBudget c delta bc+
  p+r*rowStageBudget m bm c bc p s+m*(counterBudget r bm bq+2)+10*p+8

theorem scalarVerify_exact {r c m delta p : ℕ} (br bc bm bq s : ℕ)
    (hp : 0<p) (hq : 0<bq) (hr : r≤2^br) (hc : c≤2^bc) (hm : m+1≤2^bm) (hrq : r<2^bq)
    (L : Recipes (ZMod (2^p)) r c m delta) (beta : Fin m →₀ ℕ)
    (hb : ∀ k, beta k<2^bq) (hL : ∀ j, (L.localRecipe j).length≤s)
    (hM : ∀ k, (L.moment k).length≤s) (w : Witness r c m) (d : Word p) :
    let q := scalarVerify br bc bm bq L beta w d
    (q.result=true ↔ valid (rootTerms L) beta w=true ∧ d.val<(weight (rootTerms L) w).val) ∧
    q.steps≤witnessBudget br bc bm bq s L := by
  let a := runTensors (List.ofFn w.1) (L.rows.map (packTensor br))
  let b := runTensors (List.ofFn w.2.1) (L.cols.map (packTensor bc))
  let u := runAllRows bm bc L w
  let q := checkMultiplicity bm bq beta (allocationWords bm w.2.2)
  let v := compareBits (encodeBits p d.val) u.result.2
  obtain ⟨ha,hat⟩ := runTensors_exact w.1 br p hr L.rows
  obtain ⟨hb',hbt⟩ := runTensors_exact w.2.1 bc p hc L.cols
  obtain ⟨ul,hlen,hv,hc'⟩ := runAllRows_exact bm bc s hp hm hc L w hL hM
  obtain ⟨hmc,hmt⟩ := checkMultiplicity_exact w.2.2 beta bm bq hq hm hrq hb
  change (if a.result then 1 else 0)=tensorEval w.1 L.rows at ha
  change (if b.result then 1 else 0)=tensorEval w.2.1 L.cols at hb'
  change a.steps≤_ at hat
  change b.steps≤_ at hbt
  change (u.result.1=true ↔ _) at ul
  change u.result.2.length=p at hlen
  change asResidue p u.result.2=_ at hv
  change u.steps≤_ at hc'
  change (q.result=true ↔ _) at hmc
  change q.steps≤_ at hmt
  obtain ⟨hcomp,hcost⟩ := compareBits_exact (encodeBits p d.val) u.result.2 (by
    rw [encodeBits_length,hlen])
  have hr' : (asResidue p u.result.2).val=bitsValue u.result.2 := by
    apply ZMod.val_natCast_of_lt
    have hl := bitsValue_lt u.result.2
    rwa [hlen] at hl
  change (v.result=true ↔ _) at hcomp
  rw [encodeBits_exact p d.val d.isLt,← hr'] at hcomp
  change v.steps=_ at hcost
  rw [encodeBits_length] at hcost
  have hw : weight (rootTerms L) w =
      ((if a.result then 1 else 0)*(if b.result then 1 else 0))*asResidue p u.result.2 := by
    rw [← evaluate_eq,evaluate,AOracleMachine.foldProduct_eq,← ha,← hb',hv]
  change ((a.result && b.result && u.result.1 && q.result && v.result)=true ↔ _) ∧
    a.steps+b.steps+u.steps+q.steps+v.steps+8≤witnessBudget br bc bm bq s L
  refine ⟨?_,?_⟩
  · rw [hw,valid,decide_eq_true_eq]
    cases a.result <;> cases b.result <;> simp [Bool.and_eq_true,ul,hmc,hcomp, and_left_comm, and_comm]
  · unfold witnessBudget
    omega

/-- The preexisting fixed-field parser remains the outer framing. Its
rejects contribute zero. The cost theorem above is the actual bit
execution on one correctly framed allocation, not parsing malformed
guesses or producing its coefficients. -/
def scalarVerifyCode {r c m delta p : ℕ} (br bc bm bq : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) (beta : Fin m →₀ ℕ)
    (code : Code r c bm × Word p) : Bool :=
  (parse code.1).elim false fun w => (scalarVerify br bc bm bq L beta w code.2).result

theorem scalarRegister_by_count {r c m delta p : ℕ} (br bc bm bq s : ℕ)
    (hp : 0<p) (hq : 0<bq) (hr : r≤2^br) (hc : c≤2^bc) (hm : m+1≤2^bm) (hrq : r<2^bq)
    (L : Recipes (ZMod (2^p)) r c m delta) (beta : Fin m →₀ ℕ)
    (hb : ∀ k, beta k<2^bq) (hL : ∀ j, (L.localRecipe j).length≤s)
    (hM : ∀ k, (L.moment k).length≤s) :
    (countVerify (scalarVerifyCode br bc bm bq L beta) : ZMod (2^p)) =
      MvPolynomial.coeff beta (rootPolynomial (rootTerms L)) := by
  have hf : scalarVerifyCode br bc bm bq L beta =
      verifier parse (valid (rootTerms L) beta) (weight (rootTerms L)) := by
    funext d
    unfold scalarVerifyCode verifier
    cases h : parse d.1 with
    | none => rfl
    | some w =>
      apply Bool.eq_iff_iff.mpr
      simp only [Option.elim_some,Bool.and_eq_true,decide_eq_true_eq]
      exact (scalarVerify_exact br bc bm bq s hp hq hr hc hm hrq L beta hb hL hM w d.2).1
  rw [hf,← countQuery, countQuery_residue parse (encode hm) (parse_exact hm),
    ← coefficient_eq_valid_sum]

#print axioms scalarVerify_exact
#print axioms scalarRegister_by_count
end A1R9
