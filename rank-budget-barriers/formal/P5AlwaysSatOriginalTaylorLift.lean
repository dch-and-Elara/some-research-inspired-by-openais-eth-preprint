import P5MainBalanceM6SparseEval

/-! Width-parametric source lift of the printed e_j(L) h(L)^j V^j.
The legacy width-two compiler is not used to bound width-three clauses.
The same physically typed expansion works at every ambient input. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6 P5MainBalance.M6.Sparse Polynomial
open scoped BigOperators Classical Polynomial

private theorem width_modeTerms {A : Type*} {c j k : ℕ}
    (terms : Fin c→List A) (q : Choice c j) (ht : ∀ i,(terms i).length≤k) :
    (modeTerms terms q).length≤k+2*k*j := by
  have h' (i : Fin (c+1)) : (extended terms i).length≤k := by
    refine Fin.cases ?_ (fun i=>?_) i
    · simp [extended]
    · exact ht i
  unfold modeTerms
  rw [List.length_append,length_ofFn_flatten]
  simp only [List.length_append]
  have hs :
      (∑ i : Fin j,((extended terms (q.2 i).1).length+(extended terms (q.2 i).2).length))
      ≤∑ _i : Fin j,2*k := by
    apply Finset.sum_le_sum
    intro i _
    rw [two_mul]
    exact Nat.add_le_add (h' _) (h' _)
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin] at hs
  change (∑ i : Fin j, ((extended terms (q.2 i).1).length+(extended terms (q.2 i).2).length))≤j*(2*k) at hs
  rw [Nat.mul_comm j (2*k)] at hs
  exact Nat.add_le_add (h' _) hs

variable {X W F V Copy I B : Type*} [LinearOrder B]
variable {L : SourceLayout X W F Copy I B} {mark : V↪X}

structure PrintedLift (L : SourceLayout X W F Copy I B) (mark : V↪X) (k : ℕ) where
  neutral : F→Bool
  number : F→ℕ
  terms : ∀ f,Fin (number f)→List {e : X // L.factor e=f}
  weight : ∀ f,({v : V // signedOwner L mark v=f}→Bool)→Fin (number f)→ℚ
  small : ∀ f i,(terms f i).length≤k

variable {k : ℕ}

def PrintedLift.base (P : PrintedLift L mark k) (f : F) : ℕ := if P.neutral f then 0 else k

noncomputable def PrintedLift.modeCode (P : PrintedLift L mark k) (ell : ℕ) (f : F) :
    Fin (Fintype.card (Modes ell (P.number f))) ≃ Modes ell (P.number f) :=
  (Fintype.equivFin _).symm

noncomputable def PrintedLift.modeWord (P : PrintedLift L mark k)
    (ell : ℕ) (f : F) (q : Modes ell (P.number f)) : List {e : X // L.factor e=f} :=
  if P.neutral f then [] else modeTerms (P.terms f) q.2

noncomputable def PrintedLift.modeWeightV (P : PrintedLift L mark k)
    (ell : ℕ) (f : F) (s : {v : V // signedOwner L mark v=f}→Bool)
    (q : Modes ell (P.number f)) : ℚ[X] :=
  if P.neutral f then 0 else monomial q.1.val
    (modeWeight (P.weight f s) ((printedE ell q.1).coeff 0:ℚ) ((printedE ell q.1).coeff 1:ℚ) q.2)

noncomputable def PrintedLift.termWord (P : PrintedLift L mark k) (ell : ℕ) (f : F) :
    Fin (Fintype.card (Modes ell (P.number f))+1)→List {e : X // L.factor e=f} :=
  Fin.cases [] (fun i=>P.modeWord ell f (P.modeCode ell f i))

noncomputable def PrintedLift.coeffV (P : PrintedLift L mark k)
    (ell : ℕ) (f : F) (s : {v : V // signedOwner L mark v=f}→Bool) :
    Fin (Fintype.card (Modes ell (P.number f))+1)→ℚ[X] :=
  Fin.cases (if P.neutral f then 1 else 0) (fun i=>P.modeWeightV ell f s (P.modeCode ell f i))

noncomputable def PrintedLift.compile (P : PrintedLift L mark k) (ell : ℕ) :
    SourceRecipe L mark where
  count f := Fintype.card (Modes ell (P.number f))+1
  degree f i := (P.termWord ell f i).length
  read f i j := (P.termWord ell f i).get j
  coeff f i s := P.coeffV ell f s i

set_option maxHeartbeats 9000000 in
theorem PrintedLift.graded (P : PrintedLift L mark k) (ell : ℕ) :
    (P.compile ell).graded P.base (2*k) := by
  intro f i
  refine Fin.cases ?_ (fun i=>?_) i
  · intro s j hj
    change (P.termWord ell f 0).length≤P.base f+2*k*j
    simp [PrintedLift.termWord]
  · intro s j hj
    let q := P.modeCode ell f i
    change (P.modeWord ell f q).length≤P.base f+2*k*j
    by_cases h : P.neutral f
    · simp [PrintedLift.modeWord,h]
    · have hq : q.1.val=j := by
        contrapose! hj
        change (P.modeWeightV ell f s q).coeff j=0
        simp [PrintedLift.modeWeightV,hj,h,coeff_monomial]
      simpa only [PrintedLift.modeWord,PrintedLift.base,if_neg h,hq] using
        width_modeTerms (P.terms f) q.2 (P.small f)

variable {R : Type*} [CommRing R]

noncomputable def PrintedLift.test (P : PrintedLift L mark k)
    (φ : ℚ[X]→+*R) (f : F) (s : {v : V // signedOwner L mark v=f}→Bool)
    (Y : {e : X // L.factor e=f}→R) : R :=
  sumMonomials (P.terms f) (P.weight f s) (φ.comp Polynomial.C) Y

noncomputable def liftedTest (φ : ℚ[X]→+*R) (ell : ℕ) (x : R) : R :=
  ∑ a : Fin ell,((φ.comp Polynomial.C) ((printedE ell a).coeff 0:ℚ) +
      (φ.comp Polynomial.C) ((printedE ell a).coeff 1:ℚ)*x)*(x*(x-1))^a.val * (φ Polynomial.X)^a.val

set_option maxHeartbeats 10000000 in
theorem PrintedLift.expansion (P : PrintedLift L mark k)
    (φ : ℚ[X]→+*R) (ell : ℕ) (f : F) (s : {v : V // signedOwner L mark v=f}→Bool)
    (Y : {e : X // L.factor e=f}→R) :
    (∑ i,φ (P.coeffV ell f s i)*letters (P.termWord ell f i) Y) =
      if P.neutral f then 1 else liftedTest φ ell (P.test φ f s Y) := by
  rw [Fin.sum_univ_succ]
  simp only [PrintedLift.coeffV,PrintedLift.termWord,Fin.cases_zero,Fin.cases_succ,
    letters,List.map_nil,List.prod_nil,mul_one]
  by_cases hn : P.neutral f
  · simp [hn,PrintedLift.modeWeightV]
  · simp only [hn,Bool.false_eq_true,if_false,map_zero,zero_add,PrintedLift.modeWord]
    rw [(P.modeCode ell f).sum_comp (fun q=>φ (P.modeWeightV ell f s q)*
      (List.map Y (modeTerms (P.terms f) q.2)).prod)]
    simp only [PrintedLift.modeWeightV,hn,Bool.false_eq_true,if_false]
    rw [Fintype.sum_sigma]
    unfold liftedTest PrintedLift.test
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = (∑ q : Choice (P.number f) a.val,
          (φ.comp Polynomial.C) (modeWeight (P.weight f s)
            ((printedE ell a).coeff 0:ℚ) ((printedE ell a).coeff 1:ℚ) q) *
            letters (modeTerms (P.terms f) q) Y)*(φ Polynomial.X)^a.val := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q _
        rw [←C_mul_X_pow_eq_monomial,map_mul,map_pow]
        simp only [RingHom.comp_apply,letters]
        ring
      _ = _ := by rw [mode_sum]

theorem PrintedLift.factor_literal (P : PrintedLift L mark k) (ell : ℕ)
    (f : F) (s : {v : V // signedOwner L mark v=f}→Bool) (A : X→Bivariate) :
    (P.compile ell).factorScore f s A =
      if P.neutral f then 1 else liftedTest Polynomial.C ell
        (P.test Polynomial.C f s (fun e=>A e.val)) := by
  unfold Recipe.factorScore
  change (∑ i,Polynomial.C (P.coeffV ell f s i) * ∏ j : Fin (P.termWord ell f i).length,
    A ((P.termWord ell f i).get j).val) = _
  let Y : {e : X // L.factor e=f}→Bivariate := fun e=>A e.val
  calc
    _ = ∑ i,Polynomial.C (P.coeffV ell f s i)*letters (P.termWord ell f i) Y := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z=>Polynomial.C (P.coeffV ell f s i)*z)
        (product_get_eq_letters (P.termWord ell f i) Y)
    _ = _ := P.expansion _ _ _ _ _

theorem PrintedLift.anchor_literal (P : PrintedLift L mark k) (ell : ℕ)
    (f : F) (s : {v : V // signedOwner L mark v=f}→Bool) (x : W→Bool) :
    atAnchorFactor L mark (P.compile ell) f s x =
      if P.neutral f then 1 else liftedTest (RingHom.id ℚ[X]) ell
        (P.test (RingHom.id ℚ[X]) f s (fun e=>Polynomial.C (qbits x (L.placement.owner e.val)))) := by
  unfold atAnchorFactor
  change (∑ i,(RingHom.id ℚ[X]) (P.coeffV ell f s i) *
    ∏ j : Fin (P.termWord ell f i).length,Polynomial.C
      (qbits x (L.placement.owner ((P.termWord ell f i).get j).val)))=_
  let Y : {e : X // L.factor e=f}→ℚ[X] :=
    fun e=>Polynomial.C (qbits x (L.placement.owner e.val))
  calc
    _ = ∑ i,(RingHom.id ℚ[X]) (P.coeffV ell f s i)*letters (P.termWord ell f i) Y := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z=>(RingHom.id ℚ[X]) (P.coeffV ell f s i)*z)
        (product_get_eq_letters (P.termWord ell f i) Y)
    _ = _ := P.expansion _ _ _ _ _

theorem liftedTest_at_constant (ell : ℕ) (y : ℤ) :
    liftedTest (RingHom.id ℚ[X]) ell (Polynomial.C (y:ℚ)) =
      (integerSparseFactor ell y).map (Int.castRingHom ℚ) := by
  unfold liftedTest integerSparseFactor
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Polynomial.map_monomial,←C_mul_X_pow_eq_monomial,printed_e_eval_affine]
  simp only [RingHom.id_apply,RingHom.comp_apply]
  congr 1
  change _ = Polynomial.C (((((printedE ell a).coeff 0+(printedE ell a).coeff 1*y) *
      (y*(y-1))^a.val):ℤ):ℚ)
  push_cast
  simp only [map_mul,map_add,map_sub,map_pow,map_one]

#print axioms width_modeTerms
#print axioms PrintedLift.graded
#print axioms PrintedLift.expansion
#print axioms PrintedLift.factor_literal
#print axioms PrintedLift.anchor_literal
#print axioms liftedTest_at_constant
end Paper5.AlwaysSatOriginal.Physical.Taylor