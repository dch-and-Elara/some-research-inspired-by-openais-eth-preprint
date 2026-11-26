import P5FrontendG1Literal
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Indicator

/-! Literal multivariate clause violators and their actual row sums. The
unchanged quadratic coefficient and the flipped linear coefficient are
computed in F₂, so no cancellation from the other clauses is concealed. -/
namespace Paper5.FrontendG1.Tanner
open scoped BigOperators

noncomputable def exponent {W : Type*} (S : Finset W) : W→₀ℕ :=
  Finsupp.indicator S fun _ _=>1

theorem exponent_apply {W : Type*} [DecidableEq W] (S : Finset W) (w : W) :
    exponent S w=if w∈S then 1 else 0 := by simp [exponent,Finsupp.indicator_apply]

theorem exponent_support {W : Type*} [DecidableEq W] (S : Finset W) :
    (exponent S).support=S := by
  ext w
  by_cases h : w∈S <;> simp [Finsupp.mem_support_iff,exponent_apply,h]

theorem exponent_injective (W : Type*) : Function.Injective (exponent (W:=W)) := by
  classical
  intro S T h
  simpa only [exponent_support] using congrArg Finsupp.support h

noncomputable def monomialList {W : Type*} (L : List (Finset W)) :
    MvPolynomial W F₂ :=
  (L.map fun S=>MvPolynomial.monomial (exponent S) 1).sum

theorem coeff_monomialList {W : Type*} [DecidableEq W] (L : List (Finset W)) (S : Finset W) :
    (monomialList L).coeff (exponent S)=((L.filter fun U=>decide (U=S)).length:F₂) := by
  induction L with
  | nil => simp [monomialList]
  | cons U L ih =>
    change (MvPolynomial.monomial (exponent U) 1+monomialList L).coeff (exponent S)=_
    by_cases h : U=S
    · simp [MvPolynomial.coeff_add,ih,h,add_comm]
    · simp [MvPolynomial.coeff_add,ih,h,(exponent_injective W).eq_iff]

theorem monomial_eval_mask {W : Type*} [DecidableEq W] (S x : Finset W) :
    MvPolynomial.eval (zBit ∘ wordOfMask x)
      (MvPolynomial.monomial (exponent S) (1:F₂)) = mon S x := by
  rw [MvPolynomial.eval_monomial,Finsupp.prod,exponent_support,one_mul]
  have hp : (∏ w∈S,(zBit ∘ wordOfMask x) w^exponent S w)=
       ∏ w∈S,zBit (wordOfMask x w) := by
    apply Finset.prod_congr rfl
    intro w hw
    simp [exponent_apply,hw]
  rw [hp]
  by_cases h : S⊆x
  · rw [mon,if_pos h]
    apply Finset.prod_eq_one
    intro w hw
    simp [zBit,wordOfMask,h hw]
  · obtain ⟨w,hw,hnot⟩ : ∃ w∈S,w∉x := by
      by_contra! hn
      exact h hn
    rw [mon,if_neg h]
    exact Finset.prod_eq_zero hw (by simp [zBit,wordOfMask,hnot])

theorem monomialList_eval_mask {W : Type*} [DecidableEq W] (L : List (Finset W)) (x : Finset W) :
    MvPolynomial.eval (zBit ∘ wordOfMask x) (monomialList L) =
      (L.map fun S=>mon S x).sum := by
  induction L with
  | nil => simp [monomialList]
  | cons S L ih =>
    change MvPolynomial.eval _ (MvPolynomial.monomial (exponent S) 1+monomialList L)
      = mon S x+(L.map fun U=>mon U x).sum
    rw [map_add,monomial_eval_mask,ih]

section Guarded
variable {V : Type*} [DecidableEq V]

noncomputable def violationPoly (E : Finset (V×V)) (sgn : V→Bool) (i : GuardIndex E) :
    MvPolynomial (GuardVar V) F₂ := monomialList (guardTerms E sgn i)

theorem violationPoly_eval [Fintype V] (E : Finset (V×V)) (sgn : V→Bool)
    (i : GuardIndex E) (a : GuardVar V→Bool) :
    MvPolynomial.eval (zBit ∘ a) (violationPoly E sgn i)=literalViolation E sgn a i := by
  obtain ⟨x,rfl⟩ := (maskEquiv (GuardVar V)).surjective a
  rw [violationPoly,show (maskEquiv (GuardVar V)) x=wordOfMask x from rfl,
    monomialList_eval_mask]
  exact quad_is_literal_violation E sgn x i

def zMon (v : V) : Finset (GuardVar V) := {.inr v}
def zxMon (v : V) : Finset (GuardVar V) := {.inr v,.inl v}

omit [DecidableEq V] in
private theorem zMon_as_set (v : V) : zMon v=({.inr v}:Finset (GuardVar V)) := rfl
private theorem zxMon_as_set (v : V) : zxMon v=({.inr v,.inl v}:Finset (GuardVar V)) := rfl

omit [DecidableEq V] in
@[simp] theorem zMon_eq_iff (v w : V) : zMon v=zMon w ↔ v=w := by simp [zMon]

@[simp] theorem zxMon_eq_iff (v w : V) : zxMon v=zxMon w ↔ v=w := by
  constructor
  · intro hh
    have hm : (.inr v:GuardVar V) ∈ zxMon w := by rw [←hh]; simp [zxMon]
    simpa [zxMon] using hm
  · rintro rfl
    rfl

@[simp] theorem zMon_ne_zx (v w : V) : zMon v≠zxMon w := by
  intro he
  have hx : (.inl w:GuardVar V)∈zMon v := by rw [he]; simp [zxMon]
  simp [zMon] at hx

@[simp] theorem zxMon_ne_z (v w : V) : zxMon v≠zMon w := Ne.symm (zMon_ne_zx w v)

private theorem absent_guard {U : Finset (GuardVar V)} (v : V) (h : .inr v∉U) :
    U≠zMon v ∧ U≠zxMon v := by
  constructor <;> intro he <;> rw [he] at h
  · exact h (by simp [zMon])
  · exact h (by simp [zxMon])

theorem clause_coeff_z (E : Finset (V×V)) (sgn : V→Bool) (i : GuardIndex E) (v : V) :
    (violationPoly E sgn i).coeff (exponent (zMon v)) =
      (if i=.inl v then 1 else 0) + (if i=.inr (.inl v) then zBit (sgn v) else 0) := by
  have h0 := (absent_guard v (U:=∅) (by simp)).1
  rcases i with w|(w|e)
  · by_cases h : w=v <;> simp [violationPoly,coeff_monomialList,guardTerms,←zMon_as_set,h0,h]
  · by_cases h : w=v
    · subst w
      cases hs : sgn v <;>
        simp [violationPoly,coeff_monomialList,guardTerms,←zMon_as_set,←zxMon_as_set,zBit,hs]
    · cases hs : sgn w <;>
        simp [violationPoly,coeff_monomialList,guardTerms,←zMon_as_set,←zxMon_as_set,hs,h]
  · have h1 := (absent_guard v (U:={Sum.inl e.val.1}) (by simp)).1
    have h2 := (absent_guard v (U:={Sum.inl e.val.2}) (by simp)).1
    have h3 := (absent_guard v (U:={Sum.inl e.val.1,Sum.inl e.val.2}) (by simp)).1
    simp [violationPoly,coeff_monomialList,guardTerms,h0,h1,h2,h3]

theorem clause_coeff_zx (E : Finset (V×V)) (sgn : V→Bool) (i : GuardIndex E) (v : V) :
    (violationPoly E sgn i).coeff (exponent (zxMon v)) =
      if i=.inr (.inl v) then 1 else 0 := by
  have h0 := (absent_guard v (U:=∅) (by simp)).2
  rcases i with w|(w|e)
  · simp [violationPoly,coeff_monomialList,guardTerms,←zMon_as_set,h0]
  · by_cases h : w=v
    · subst w
      cases hs : sgn v <;>
        simp [violationPoly,coeff_monomialList,guardTerms,←zMon_as_set,←zxMon_as_set,hs]
    · cases hs : sgn w <;>
        simp [violationPoly,coeff_monomialList,guardTerms,←zMon_as_set,←zxMon_as_set,h,hs]
  · have h1 := (absent_guard v (U:={Sum.inl e.val.1}) (by simp)).2
    have h2 := (absent_guard v (U:={Sum.inl e.val.2}) (by simp)).2
    have h3 := (absent_guard v (U:={Sum.inl e.val.1,Sum.inl e.val.2}) (by simp)).2
    simp [violationPoly,coeff_monomialList,guardTerms,h0,h1,h2,h3]

variable [Fintype V]

noncomputable def rowPoly (E : Finset (V×V)) (sgn : V→Bool) (w : GuardIndex E→F₂) :
    MvPolynomial (GuardVar V) F₂ := ∑ i, MvPolynomial.C (w i)*violationPoly E sgn i

theorem evaluated_rowPoly {R : Type*} (E : Finset (V×V)) (sgn : V→Bool)
    (A : Matrix R (GuardIndex E) F₂) (a : GuardVar V→Bool) (r : R) :
    MvPolynomial.eval (zBit ∘ a) (rowPoly E sgn (A r))=(A.mulVec (literalViolation E sgn a)) r := by
  simp [rowPoly,violationPoly_eval,Matrix.mulVec,dotProduct]

theorem row_coeff_z (E : Finset (V×V)) (sgn : V→Bool) (w : GuardIndex E→F₂) (v : V) :
    (rowPoly E sgn w).coeff (exponent (zMon v)) =
      w (.inl v)+w (.inr (.inl v))*zBit (sgn v) := by
  simp [rowPoly,MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul,clause_coeff_z,
    mul_ite]

theorem row_coeff_zx (E : Finset (V×V)) (sgn : V→Bool) (w : GuardIndex E→F₂) (v : V) :
    (rowPoly E sgn w).coeff (exponent (zxMon v))=w (.inr (.inl v)) := by
  simp [rowPoly,MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul,clause_coeff_zx,mul_ite]

private theorem bit_flip : ∀ b : Bool,zBit (!b)=zBit b+1 := by decide
private theorem add_one_moves : ∀ a : F₂,a+1≠a := by decide

/-- The same row index, arbitrary other columns, and arbitrary other signs. -/
theorem sign_flip_preserves_quadratic (E : Finset (V×V)) (sgn : V→Bool)
    (w : GuardIndex E→F₂) (v : V) (hRead : w (.inr (.inl v))=1) :
    let s' := Function.update sgn v (!sgn v)
    (rowPoly E s' w).coeff (exponent (zMon v)) ≠
        (rowPoly E sgn w).coeff (exponent (zMon v)) ∧
    (rowPoly E s' w).coeff (exponent (zxMon v))=1 ∧
    (rowPoly E sgn w).coeff (exponent (zxMon v))=1 := by
  simp only [row_coeff_z,row_coeff_zx,hRead,one_mul,Function.update_self,bit_flip]
  rw [←add_assoc]
  exact ⟨add_one_moves _,trivial,trivial⟩

end Guarded

#print axioms exponent_apply
#print axioms exponent_support
#print axioms exponent_injective
#print axioms coeff_monomialList
#print axioms monomial_eval_mask
#print axioms monomialList_eval_mask
#print axioms violationPoly_eval
#print axioms zMon_eq_iff
#print axioms zxMon_eq_iff
#print axioms zMon_ne_zx
#print axioms zxMon_ne_z
#print axioms clause_coeff_z
#print axioms clause_coeff_zx
#print axioms evaluated_rowPoly
#print axioms row_coeff_z
#print axioms row_coeff_zx
#print axioms sign_flip_preserves_quadratic
end Paper5.FrontendG1.Tanner