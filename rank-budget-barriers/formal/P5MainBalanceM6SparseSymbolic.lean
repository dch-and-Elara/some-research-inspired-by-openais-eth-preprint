import P5MainBalanceM6SparseCompiler

/-! Equality before the deformation is removed: arbitrary rational
polynomial port inputs, not merely Boolean anchor evaluations. The
physical V is the inner variable, C(X), of the true bivariate ring. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial
open scoped BigOperators Classical Polynomial

variable {E W F Copy I B V : Type*} [LinearOrder B]
variable {L : SourceLayout E W F Copy I B} {mark : V↪E}

noncomputable def innerRat : ℚ→+*Bivariate := (C : ℚ[X]→+*Bivariate).comp (C : ℚ→+*ℚ[X])

noncomputable def LiftSource.testPolynomial (P : LiftSource L mark) (f : F)
    (s : {v : V // signedOwner L mark v=f}→Bool) (input : E→Bivariate) : Bivariate :=
  sumMonomials (P.terms f) (P.weight f s) innerRat (fun e=>input e.val)

set_option maxHeartbeats 8000000 in
theorem LiftSource.compile_factor_sum (P : LiftSource L mark) (ell : ℕ) (f : F)
    (s : {v : V // signedOwner L mark v=f}→Bool) (input : E→Bivariate) :
    (P.compile ell).factorScore f s input =
      (if P.neutral f then 1 else (∑ q : Modes ell (P.number f),
        C (P.modeCoeff ell f s q) * letters (modeTerms (P.terms f) q.2) (fun e=>input e.val))) := by
  unfold Recipe.factorScore
  let Y : {e : E // L.factor e=f}→Bivariate := fun e=>input e.val
  change (∑ i : Fin (Fintype.card (Modes ell (P.number f))+1),
    C (Fin.cases (if P.neutral f then 1 else 0) (fun k=>P.modeCoeff ell f s (P.modeCode ell f k)) i) *
      ∏ j : Fin (P.termList ell f i).length,Y ((P.termList ell f i).get j))=_
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,product_get_eq_letters,LiftSource.termList,letters,
    List.map_nil,List.prod_nil,mul_one]
  by_cases h : P.neutral f
  · simp [h,LiftSource.modeCoeff]
  · simp only [h,Bool.false_eq_true,if_false,map_zero,zero_add,LiftSource.modeList]
    exact (P.modeCode ell f).sum_comp (fun q : Modes ell (P.number f) =>
      C (P.modeCoeff ell f s q) * letters (modeTerms (P.terms f) q.2) Y)

noncomputable def liftedPolynomial (ell : ℕ) (Y : Bivariate) : Bivariate :=
  ∑ a : Fin ell,
    (printedE ell a).eval₂ (Int.castRingHom Bivariate) Y *
      (Y*(Y-1))^a.val * (C (X:ℚ[X]))^a.val

set_option maxHeartbeats 15000000 in
theorem LiftSource.compiler_is_printed_lift (P : LiftSource L mark) (ell : ℕ) (f : F)
    (s : {v : V // signedOwner L mark v=f}→Bool) (input : E→Bivariate) :
    (P.compile ell).factorScore f s input =
      if P.neutral f then 1 else liftedPolynomial ell (P.testPolynomial f s input) := by
  rw [P.compile_factor_sum]
  by_cases h : P.neutral f
  · simp only [h,if_true]
  · have h' : P.neutral f=false := Bool.eq_false_of_not_eq_true h
    simp only [h',Bool.false_eq_true,if_false,LiftSource.modeCoeff,liftedPolynomial]
    rw [Fintype.sum_sigma]
    simp_rw [←C_mul_X_pow_eq_monomial,map_mul,map_pow]
    apply Finset.sum_congr rfl
    intro a _
    let Y : {e : E // L.factor e=f}→Bivariate := fun e => input e.val
    let aa : ℚ := ((printedE ell a).coeff 0:ℚ)
    let bb : ℚ := ((printedE ell a).coeff 1:ℚ)
    calc
      _ = (∑ q : Choice (P.number f) a.val,innerRat (modeWeight (P.weight f s) aa bb q) *
          letters (modeTerms (P.terms f) q) Y)*(C (X:ℚ[X]))^a.val := by
        rw [Finset.sum_mul]
        have hterm (q : Choice (P.number f) a.val) :
            (innerRat (modeWeight (P.weight f s) aa bb q) * C (X:ℚ[X])^a.val)*
                letters (modeTerms (P.terms f) q) Y =
              (innerRat (modeWeight (P.weight f s) aa bb q) * letters (modeTerms (P.terms f) q) Y)*
                C (X:ℚ[X])^a.val := mul_right_comm _ _ _
        exact Finset.sum_congr rfl (fun q _=>hterm q)
      _ = _ := by
        rw [mode_sum]
        have ha : innerRat aa=(Int.castRingHom Bivariate) ((printedE ell a).coeff 0) := by
          simp [innerRat,aa]
        have hb : innerRat bb=(Int.castRingHom Bivariate) ((printedE ell a).coeff 1) := by
          simp [innerRat,bb]
        rw [ha,hb]
        have hAffine := congrArg
          (fun q : ℤ[X]=>q.eval₂ (Int.castRingHom Bivariate) (P.testPolynomial f s input))
          (printed_e_affine ell a.val)
        simp only [eval₂_add,eval₂_mul,eval₂_C,eval₂_X] at hAffine
        rw [hAffine]
        rfl

#print axioms LiftSource.compile_factor_sum
#print axioms LiftSource.compiler_is_printed_lift
end P5MainBalance.M6.Sparse
