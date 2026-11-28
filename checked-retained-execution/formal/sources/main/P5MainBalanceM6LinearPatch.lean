import P5MainBalanceBooleanDifference
import Mathlib.Data.Fintype.Option

/-! A physical replacement form can depend on every auxiliary Boolean
input. The support lemma is therefore extended from single-coordinate
patches to arbitrary linear vector corrections and arbitrary polynomial
factors, with no multilinearity hypothesis on a factor. -/
namespace P5MainBalance.M6
open P5MainBalance Polynomial
open scoped BigOperators Classical

variable {W D R : Type*} [Fintype W] [Nonempty W] [CommRing R]

noncomputable def window (x : Finset W) (j : ℕ) (F : Finset W→R) : R :=
  ∑ S∈x.powerset.filter (fun S=>S.card≤j),
    ∑ U∈S.powerset,(-1:R)^((S\U).card)*F U

omit [Fintype W] [Nonempty W] in
theorem window_sum {T : Type*} (L : Finset T) (x : Finset W) (j : ℕ)
    (F : T→Finset W→R) :
    window x j (fun U=>∑ a∈L,F a U)=∑ a∈L,window x j (F a) := by
  unfold window
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  exact Finset.sum_comm

omit [Fintype W] [Nonempty W] in
theorem window_mul (x : Finset W) (j : ℕ) (a : R) (F : Finset W→R) :
    window x j (fun U=>a*F U)=a*window x j F := by
  unfold window
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro U _
  ring

noncomputable def linearPatch (base : D→R[X]) (δ : D→W→R[X])
    (U : Finset W) (e : D) : R[X] :=
  (∑ w : W,if w∈U then X*δ e w else 0)+base e

omit [Nonempty W] in
theorem linearPatch_option (base : D→R[X]) (δ : D→W→R[X])
    (U : Finset W) (e : D) :
    linearPatch base δ U e=
      ∑ w : Option W, w.elim (base e) (fun w=>if w∈U then X*δ e w else 0) := by
  rw [Fintype.sum_option]
  exact add_comm _ _

set_option maxHeartbeats 9000000 in
theorem linear_patches_have_small_window [Fintype D] (base : D→R[X]) (δ : D→W→R[X])
    (x : Finset W) (j : ℕ) :
    ((∏ e,linearPatch base δ x e).coeff j) =
      window x j (fun U=> (∏ e,linearPatch base δ U e).coeff j) := by
  let owner : (D→Option W)→D→W := fun p e=>(p e).getD (Classical.choice inferInstance)
  let b : (D→Option W)→D→R[X] := fun p e=> (p e).elim (base e) (fun _=>0)
  let d : (D→Option W)→D→R[X] := fun p e=> (p e).elim 0 (δ e)
  have h (U : Finset W) :
      (∏ e,linearPatch base δ U e) =
        ∑ p : D→Option W,patchProduct (owner p) (b p) (d p) (boolSet U) := by
    simp_rw [linearPatch_option]
    rw [Fintype.prod_sum (fun e (w : Option W)=>
      w.elim (base e) (fun w=>if w∈U then X*δ e w else 0))]
    apply Finset.sum_congr rfl
    intro p _
    unfold patchProduct
    apply Finset.prod_congr rfl
    intro e _
    cases hp : p e with
    | none => simp [hp,owner,b,d]
    | some w =>
      by_cases hw : w∈U <;> simp [hp,owner,b,d,hw,boolSet]
  simp_rw [h,finset_sum_coeff,window_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact patch_eval_by_small_pairs (owner p) (b p) (d p) j x

/-- Sums of weighted monomial products inherit the same small-window
identity. Repeated incidence positions and exponents are allowed. -/
theorem monomial_menu_has_small_window {T : Type*} [Fintype T] (Arity : T→ℕ)
    (read : ∀ t,Fin (Arity t)→D) (weight : T→R)
    (base : D→R[X]) (δ : D→W→R[X]) (x : Finset W) (j : ℕ) :
    ((∑ a:T,C (weight a)*∏ e,linearPatch base δ x (read a e)).coeff j) =
      window x j (fun U=>(∑ a:T,C (weight a)*∏ e,linearPatch base δ U (read a e)).coeff j) := by
  simp_rw [finset_sum_coeff,coeff_C_mul,window_sum,window_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun z=>weight a*z)
    (linear_patches_have_small_window (base∘read a) (fun e=>δ (read a e)) x j)

#print axioms window_sum
#print axioms window_mul
#print axioms linear_patches_have_small_window
#print axioms monomial_menu_has_small_window
end P5MainBalance.M6
