import V8NativeMessageN8LiteralPayload
import V8NativeMessageN4PhysicalTarget

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3300000

/-! The distinguishing rows are the actual terminal CNF count on N4's
matched pin bits. Unmatched original pins are TRUE; the target is OR,
not the five-copy identity parity matrix. -/
namespace V8NativeMessage.N8Literal
open scoped Classical BigOperators Polynomial
open Polynomial V8NativeMessage.N4 Paper5.D1Literal Paper5.HybridClosure

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {reg : ∀v,GraphCutMoments.degree F v=3}
variable {f : ℤ[X]} {P : RootPacking F reg f} {i : rootKept F f}
variable {γ : ℝ} (C : FourCut P i γ)

def matchedRowWord (x : Fin C.m→Bool) : RowWord P i C.T :=
  fun v => restriction C.pairs x (fun _=>true) v.val
def matchedColWord (y : Fin C.m→Bool) : ColWord P i C.T :=
  fun v => restriction C.pairs (fun _=>true) y v.val

theorem original_matching_splice (x y : Fin C.m→Bool) :
    mergeSigns P i C.T (matchedRowWord C x) (matchedColWord C y)=
      restriction C.pairs x y := by
  funext v
  by_cases h : v∈Set.range C.pairs.seat
  · obtain ⟨⟨j,b⟩,rfl⟩ := h
    cases b
    · simp only [mergeSigns,matchedRowWord,dif_pos (C.left j),restriction_on,Bool.false_eq_true,if_false]
    · simp only [mergeSigns,matchedColWord,dif_neg (C.right j),restriction_on,if_true]
  · by_cases hgroup : pinGroup P i v∈C.T
    · simp only [mergeSigns,dif_pos hgroup,matchedRowWord,restriction_off _ _ _ _ h]
    · simp only [mergeSigns,dif_neg hgroup,matchedColWord,restriction_off _ _ _ _ h]

def separateColumn (j : Fin C.m) : Fin C.m→Bool :=
  fun k => if k=j then false else true

theorem actual_count_separates_at (x : Fin C.m→Bool) (j : Fin C.m) :
    nativeCount F reg (restriction C.pairs x (separateColumn C j)) =
      if x j then 1 else 0 := by
  rw [literal_count_on_matching C.pairs]
  rw [Finset.prod_eq_single j]
  · simp [separateColumn]
  · intro k _ hk
    simp [separateColumn,hk]
  · simp

theorem actual_count_rows_distinct (x x' : Fin C.m→Bool)
    (same : ∀ y, (nativeCount F reg (restriction C.pairs x y):ZMod 2) =
      (nativeCount F reg (restriction C.pairs x' y):ZMod 2)) : x=x' := by
  funext j
  have h := same (separateColumn C j)
  rw [actual_count_separates_at C x j,actual_count_separates_at C x' j] at h
  cases hx : x j <;> cases hx' : x' j <;> simp [hx,hx'] at h ⊢

#print axioms original_matching_splice
#print axioms actual_count_separates_at
#print axioms actual_count_rows_distinct
end
end V8NativeMessage.N8Literal
