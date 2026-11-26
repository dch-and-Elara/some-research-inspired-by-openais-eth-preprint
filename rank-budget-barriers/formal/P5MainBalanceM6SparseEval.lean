import P5MainBalanceM6SparseCompiler

/-! The literal compiled sparse coefficients, evaluated on Boolean
inputs, are exactly the rational image of the integer source lift. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial
open scoped BigOperators Classical Polynomial

variable {A K R : Type*} [CommRing K] [CommRing R]

theorem letters_mapped (hh : K→+*R) (p : List A) (Y : A→K) :
    letters p (hh∘Y)=hh (letters p Y) := by
  unfold letters
  rw [←List.map_map]
  exact (map_list_prod hh _).symm

theorem sumMonomials_mapped {c : ℕ} (p : Fin c→List A) (w : Fin c→ℚ)
    (hh : ℚ→+*K) (Y : A→ℚ) :
    sumMonomials p w hh (hh∘Y)=hh (sumMonomials p w (RingHom.id ℚ) Y) := by
  unfold sumMonomials
  rw [map_sum]
  simp only [map_mul,letters_mapped,RingHom.id_apply]

variable {E W F Copy I B V : Type*} [LinearOrder B]
variable {L : SourceLayout E W F Copy I B} {mark : V↪E}

set_option maxHeartbeats 9000000 in
theorem LiftSource.anchor_compiled_of_evenTest
    (P : LiftSource L mark) (ell : ℕ) (f : F)
    (s : {v : V // signedOwner L mark v=f}→Bool) (x : W→Bool) (y : ℤ)
    (h : P.neutral f=false)
    (hh : P.anchorTest f s x=(y:ℚ)) :
    atAnchorFactor L mark (P.compile ell) f s x =
      (integerSparseFactor ell y).map (Int.castRingHom ℚ) := by
  let Y : {e : E // L.factor e=f}→ℚ[X] :=
    fun e=>C (qbits x (L.placement.owner e.val))
  rw [LiftSource.compile_anchor_sum]
  simp only [h,Bool.false_eq_true,if_false,LiftSource.modeCoeff]
  rw [Fintype.sum_sigma]
  unfold integerSparseFactor
  rw [Polynomial.map_sum]
  simp_rw [Polynomial.map_monomial,←C_mul_X_pow_eq_monomial]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = (∑ q : Choice (P.number f) a.val,
        C (modeWeight (P.weight f s) ((printedE ell a).coeff 0:ℚ) ((printedE ell a).coeff 1:ℚ) q) *
        letters (modeTerms (P.terms f) q) Y)*X^a.val := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by
      rw [mode_sum]
      have he : sumMonomials (P.terms f) (P.weight f s) (C : ℚ→+*ℚ[X]) Y=C (y:ℚ) := by
        change sumMonomials _ _ _ (C ∘ fun e : {e : E // L.factor e=f}=>qbits x (L.placement.owner e.val))=_
        rw [sumMonomials_mapped]
        change C (P.anchorTest f s x)=_
        rw [hh]
      rw [he,printed_e_eval_affine]
      congr 1
      have hOne : (1:ℚ[X])=C (1:ℚ) := (map_one C).symm
      rw [hOne,←map_sub C,←map_mul C (y:ℚ) ((y:ℚ)-1),←map_pow C,←map_mul C,←map_add C,←map_mul C]
      congr 1
      change _ = (((((printedE ell a).coeff 0+(printedE ell a).coeff 1*y) * (y*(y-1))^a.val):ℤ):ℚ)
      push_cast
      rfl

theorem LiftSource.anchor_compiled_neutral
    (P : LiftSource L mark) (ell : ℕ) (f : F)
    (s : {v : V // signedOwner L mark v=f}→Bool) (x : W→Bool)
    (h : P.neutral f=true) :
    atAnchorFactor L mark (P.compile ell) f s x=1 := by
  rw [LiftSource.compile_anchor_sum]
  simp only [h,if_true]

#print axioms sumMonomials_mapped
#print axioms LiftSource.anchor_compiled_of_evenTest
#print axioms LiftSource.anchor_compiled_neutral
end P5MainBalance.M6.Sparse
