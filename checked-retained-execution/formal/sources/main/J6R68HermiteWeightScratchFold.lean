import J6R68HermiteWeightScratchInverse
import J6R23ScheduleWeightFold

/-! Actual pre-inversion native fold. At a cut, the pending Part
values are exactly the prefix's already evaluated signed factors;
the nested call is the original fold on the suffix. The footprint
counts the odd residue blocks, not the full denotational integers
or an assumed encoding of the separate Nat valuation metadata. -/
namespace J6R68.HermiteWeightScratch
open scoped Polynomial
open A1R10 A1R11 A1R12 AOracleMachineTime J6R23ScheduleWeight
open J6R21Leaf J6R50NonModeScratch
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 5900000

variable {p ell : ℕ} {fw : List (Word p)}

def weightFactor (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a : ℕ) (t : ℤ) (b : Side) (q : ℤ×ℕ) : Meter (Part fw ell) :=
  powerPart hp he hv (a+1) q.2 (signedFactor t b q.1)

def foldPartReturn (hp : 0<p) (a : ℕ)
    (left right : Meter (Part fw ell)) : Meter (Part fw ell) :=
  let out := uvMul hp left.result.odd right.result.odd
  let T := left.result.two+right.result.two
  ⟨⟨T,out.result⟩,left.steps+right.steps+out.steps+8*(a+T+3)^2+10⟩

def resumeParts (hp : 0<p) (a : ℕ)
    (saved : List (Meter (Part fw ell))) (later : Meter (Part fw ell)) : Meter (Part fw ell) :=
  saved.foldr (foldPartReturn hp a) later

theorem source_fold_retains_exact_already_computed_factors
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a : ℕ) (t : ℤ) (b : Side) (before after : List (ℤ×ℕ)) :
    foldParts hp he hv a t b (before++after)=
      resumeParts hp a (before.map (weightFactor hp he hv a t b))
        (foldParts hp he hv a t b after) := by
  induction before with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.cons_append,foldParts,List.map_cons,resumeParts,List.foldr_cons,
      foldPartReturn,weightFactor] at ih ⊢
    rw [ih]

theorem actual_signed_fold_named_mul_cut
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (a : ℕ) (t : ℤ) (b : Side) (before after : List (ℤ×ℕ)) (q : ℤ×ℕ)
    (retained : List (UVBlock fw ell))
    (pre : List (UBlock fw)) (h : UBlock fw) (tail : List (UBlock fw))
    (cut : (weightFactor hp he hv a t b q).result.odd.val=pre++h::tail) :
    let saved := before.map (weightFactor hp he hv a t b)
    let left := weightFactor hp he hv a t b q
    let right := foldParts hp he hv a t b after
    let operands := weightBlocks (retained++(saved.map (fun f=>f.result.odd))++[left.result.odd,right.result.odd])
    let arrays := encodeArrays scalarPayload (combineArrays (uGates hp fw) h tail right.result.odd.val)
    foldParts hp he hv a t b (before++q::after)=resumeParts hp a saved (foldPartReturn hp a left right) ∧
      operands.length=(retained.length+before.length+2)*(ell*(fw.length*p)) ∧
      (operands++arrays).length≤(retained.length+before.length+2)*(ell*(fw.length*p))+(10*ell)*(fw.length*p) := by
  let saved := before.map (weightFactor hp he hv a t b)
  let left := weightFactor hp he hv a t b q
  let right := foldParts hp he hv a t b after
  let operands := weightBlocks (retained++(saved.map (fun f=>f.result.odd))++[left.result.odd,right.result.odd])
  have same := source_fold_retains_exact_already_computed_factors hp he hv a t b before (q::after)
  have width : operands.length=(retained.length+before.length+2)*(ell*(fw.length*p)) := by
    unfold operands
    rw [weight_block_payload_exact]
    simp only [List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.reduceAdd,saved]
  have array := native_v_convolution_scratch hp left.result.odd right.result.odd pre h tail cut
  refine ⟨same,width,?_⟩
  change (operands++encodeArrays scalarPayload (combineArrays (uGates hp fw) h tail right.result.odd.val)).length≤_
  rw [List.length_append,width]
  exact Nat.add_le_add_left array _

#print axioms source_fold_retains_exact_already_computed_factors
#print axioms actual_signed_fold_named_mul_cut
end J6R68.HermiteWeightScratch
