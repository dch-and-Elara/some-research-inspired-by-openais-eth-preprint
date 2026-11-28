
import J6R21LeafWidth

/-! The two actual schoolbook convolutions respect finite raw bit
widths before monic elimination and V-truncation, not just on their
final quotient registers. -/
namespace J6R21Leaf
open AOracleMachineTime AOracleCoordinates A1R10
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2600000

private theorem length_flatten_eq {A B : Type} (s : List A) (f : A→List B) (b : ℕ)
    (h : ∀ x∈s,(f x).length=b) : (s.flatMap f).length=s.length*b := by
  induction s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    rw [h x List.mem_cons_self,ih (fun y hy=>h y (List.mem_cons_of_mem _ hy)),Nat.add_comm]

theorem inner_convolution_payload_width {p : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (a b : UBlock fw) :
    (((convolve (wordOps p hp).toGates a.val b.val).result).flatMap Subtype.val).length =
      (2*fw.length)*p := by
  have h := (convolve_exact (wordOps p hp) a.val b.val).1
  rw [a.property,b.property] at h
  rw [length_flatten_eq _ _ p (fun x _=>x.property),h,two_mul]

theorem outer_convolution_payload_width {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (a b : UVBlock fw ell) :
    (((convolve (uGates hp fw) a.val b.val).result).flatMap scalarPayload).length =
      (2*ell)*(fw.length*p) := by
  have h := (convolve_exact (uOps hp fw) a.val b.val).1
  rw [a.property,b.property] at h
  rw [length_flatten_eq _ _ (fw.length*p) (fun x _=>scalar_payload_width x)]
  change (convolve (uOps hp fw).toGates a.val b.val).result.length*(fw.length*p)=_
  rw [h,two_mul]

#print axioms inner_convolution_payload_width
#print axioms outer_convolution_payload_width
end J6R21Leaf
