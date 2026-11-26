import P5MainBalanceM6Scores
import P5MainBalanceM6Trim

/-! At the undeformed anchor, the actual copied row is exactly its
original Boolean variable. This removes any opaque source H(0)
evaluation identity; correctness of the particular CNF factor list
is a separate, local factor property. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial
open scoped BigOperators Classical

variable {E W F Copy I B V : Type*} [Fintype E] [Fintype W] [Fintype F]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def atAnchorFactor (L : SourceLayout E W F Copy I B) (mark : V↪E)
    (P : SourceRecipe L mark) (f : F)
    (σ : {v : V//signedOwner L mark v=f}→Bool) (x : W→Bool) : ℚ[X] :=
  ∑ k,P.coeff f k σ * ∏ j,C (qbits x (L.placement.owner (P.read f k j).val))

set_option maxHeartbeats 3300000 in
omit [Fintype F] in
theorem originalInput_constant (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (x : W→Bool) (e : E) :
    Polynomial.constantCoeff (originalInput L t M x e)=
      C (qbits x (L.placement.owner e)) := by
  unfold originalInput
  change (((physicalRow L t M e (qbits x)).map (C : ℚ→+*ℚ[X])).coeff 0)=_
  rw [coeff_map,coeff_zero_eq_eval_zero,physicalRow_zero]

theorem actual_anchor_is_source_sum (L : SourceLayout E W F Copy I B) (mark : V↪E)
    (t : I→ℚ) (M : Mix Copy I B) (P : SourceRecipe L mark) (σ : V→Bool) :
    (actualH L mark t M P σ).coeff 0 =
      ∑ x : W→Bool,∏ f,∑ k,P.coeff f k (fun v=>σ v.val) *
        ∏ j,C (qbits x (L.placement.owner (P.read f k j).val)) := by
  change Polynomial.constantCoeff (actualH L mark t M P σ)=_
  have hC (p : ℚ[X]) : Polynomial.constantCoeff (C p:Bivariate)=p := coeff_C_zero
  unfold actualH Recipe.evaluate Recipe.factorScore
  simp only [map_sum,map_prod,map_mul,hC,originalInput_constant]

noncomputable def nativeModelCount (good : (W→Bool)→Prop) : ℕ :=
  Fintype.card {x : W→Bool // good x}

set_option maxHeartbeats 5500000 in
theorem direct_anchor_count_from_literal_factors
    (L : SourceLayout E W F Copy I B) (mark : V↪E)
    (t : I→ℚ) (M : Mix Copy I B) (P : SourceRecipe L mark)
    (good : ∀ f : F,({v : V // signedOwner L mark v=f}→Bool)→(W→Bool)→Prop)
    (hLocal : ∀ f s x,atAnchorFactor L mark P f s x=(if good f s x then 1 else 0))
    (σ : V→Bool) :
    retainedOrigin 1 (actualH L mark t M P σ)=
      (nativeModelCount (fun x=>∀ f,good f (fun v=>σ v.val) x):ℚ) := by
  let g (x : W→Bool) : Prop := ∀ f,good f (fun v=>σ v.val) x
  have hProd (x : W→Bool) :
      (∏ f,atAnchorFactor L mark P f (fun v=>σ v.val) x) =
        if g x then (1:ℚ[X]) else 0 := by
    by_cases h : g x
    · rw [if_pos h]
      exact Finset.prod_eq_one (fun f _=>(hLocal f _ _).trans (if_pos (h f)))
    · rw [if_neg h]
      obtain ⟨f,hf⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ f) ((hLocal f _ _).trans (if_neg hf))
  have hp :
      (actualH L mark t M P σ).coeff 0 =
        ∑ x : W→Bool, if g x then (1:ℚ[X]) else 0 := by
    rw [actual_anchor_is_source_sum]
    exact Finset.sum_congr rfl (fun x _=>hProd x)
  unfold retainedOrigin nativeModelCount
  rw [hp]
  change (∑ s : Fin 1,(_ : ℚ[X]).coeff s) = _
  simp only [Fin.sum_univ_one,Fin.val_zero,finset_sum_coeff]
  have hBool (x : W→Bool) : (if g x then (1:ℚ[X]) else 0).coeff 0 =
      if g x then (1:ℚ) else 0 := by by_cases h : g x <;> simp [h]
  simp_rw [hBool]
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 1
  rw [Fintype.card_subtype]

#print axioms originalInput_constant
#print axioms actual_anchor_is_source_sum
#print axioms direct_anchor_count_from_literal_factors
end P5MainBalance.M6
