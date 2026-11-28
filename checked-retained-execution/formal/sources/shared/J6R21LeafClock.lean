
import J6R21LeafReverse
import J6R21LeafPhysical

/-! The real depth-first controller follows a sequential edge-count
tape rather than invoking an uncharged binary Nat decrement. The root
serial directory supplies a tape of exactly the live edge count. -/
namespace J6R21Leaf
open AOracleMachineTime A1R10 A1R12

def clockDFS {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (read : List Bool→Meter (UVBlock fw ell)) :
    List Unit→List Bool→Meter (UVBlock fw ell)
  | [],rev =>
    let t := reverseTape rev []
    padCost (read t.result) t.steps
  | _::more,rev => padCost (addM hp (clockDFS hp read more (false::rev))
      (clockDFS hp read more (true::rev))) 4

theorem clockDFS_agrees {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (read : List Bool→Meter (UVBlock fw ell)) (clock : List Unit) (rev : List Bool) :
    clockDFS hp read clock rev=enumerate hp read clock.length rev := by
  rw [← exactBitDFS_public]
  induction clock generalizing rev with
  | nil => rfl
  | cons a c ih => simp only [clockDFS,List.length_cons,exactBitDFS,ih]

theorem clocked_leaf_is_native_enumerator {p ell m : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) {V : Type} (nodes : List V)
    (query : V→List Bool→Meter (UVBlock fw ell))
    (clock : List Unit) (h : clock.length=m) :
    clockDFS hp (readProduct hp he hv nodes query) clock [] = leafCompute hp he hv m nodes query := by
  rw [clockDFS_agrees,h,leafCompute]

#print axioms clockDFS_agrees
#print axioms clocked_leaf_is_native_enumerator
end J6R21Leaf
