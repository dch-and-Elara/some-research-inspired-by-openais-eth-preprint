import V8CapacityFeatures

/-! Exact finite raw feature span for the original A1 receiver polynomial.
A larger rectangular exponent index is harmless: all total-degree
outliers are proven zero at precision P rather than silently dropped. -/
namespace V8CapacityFeatureSpan
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityCRTJet V8CapacityTranslation V8CapacityFeatures

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {R H : Type*} [CommRing R] [IsLocalRing R] [Fintype H]

abbrev ExponentBox (H : Type*) (D : ℕ) := H → Fin (D+1)
abbrev FeatureBox (H : Type*) (D k : ℕ) := ExponentBox H D × Fin k

def topRead (π : R) (P k : ℕ) (F : MvPolynomial H (Jet R k)) (c : H → ℕ → R) : BaseMod R π P :=
  coefficient (BaseMod R π P) k (k-1) (MvPolynomial.eval₂Hom (reduceJet R π P k)
    (digitShift R π P k c) F)

theorem topRead_add (π : R) (P k : ℕ) (F G : MvPolynomial H (Jet R k)) (c : H → ℕ → R) :
    topRead π P k (F+G) c=topRead π P k F c+topRead π P k G c := by
  simp only [topRead,map_add,coefficient,Polynomial.coeff_add]

theorem topRead_monomial_mk (π : R) (P k : ℕ) (hk : 0<k)
    (d : H →₀ ℕ) (g : R[X]) (c : H → ℕ → R) :
    topRead π P k (MvPolynomial.monomial d (AdjoinRoot.mk ((X:R[X])^k) g)) c =
      coeffMod R π P
        (((∏ i : H, shiftedPolynomial π k (c i)^d i : R[X])*g).coeff (k-1)) := by
  unfold topRead
  rw [MvPolynomial.eval₂Hom_monomial,Finsupp.prod_pow,source_reduce_mk]
  let f : R[X] →+* FiniteJet R π P k :=
    (AdjoinRoot.mk ((X:(BaseMod R π P)[X])^k)).comp (Polynomial.mapRingHom (coeffMod R π P))
  have he (i : H) : digitShift R π P k c i=f (shiftedPolynomial π k (c i)) := finite_shift_is_mk π P k c i
  simp_rw [he,← map_pow]
  rw [← map_prod f]
  change coefficient (BaseMod R π P) k (k-1)
    (f g * f (∏ i : H, shiftedPolynomial π k (c i)^d i))=_
  rw [← map_mul, mul_comm g]
  change coefficient (BaseMod R π P) k (k-1)
    (AdjoinRoot.mk ((X:(BaseMod R π P)[X])^k)
      (((∏ i : H, shiftedPolynomial π k (c i)^d i : R[X])*g).map (coeffMod R π P)))=_
  rw [coefficient_mk k (k-1) (by omega),Polynomial.coeff_map]

theorem topRead_monomial_sum (π : R) (P k : ℕ) (hk : 0<k)
    (d : H →₀ ℕ) (g : R[X]) (c : H → ℕ → R) :
    topRead π P k (MvPolynomial.monomial d (AdjoinRoot.mk ((X:R[X])^k) g)) c =
      ∑ j : Fin k, coeffMod R π P (g.coeff (k-1-j.val))*
        coeffMod R π P (rawFeature π k d j c) := by
  rw [topRead_monomial_mk π P k hk,Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (∏ e : H, shiftedPolynomial π k (c e)^d e : R[X]).coeff i*g.coeff j)]
  rw [show (k-1).succ=k by omega,map_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul,rawFeature,mul_comm]

theorem monomial_over_degree_zero (π : R) (P k : ℕ) (hk : 0<k)
    (d : H →₀ ℕ) (g : R[X]) (c : H → ℕ → R) (hd : P+k-1≤∑ i : H,d i) :
    topRead π P k (MvPolynomial.monomial d (AdjoinRoot.mk ((X:R[X])^k) g)) c=0 := by
  rw [topRead_monomial_sum π P k hk]
  apply Finset.sum_eq_zero
  intro j _
  have hj := j.isLt
  have hzero : coeffMod R π P (rawFeature π k d j c)=0 := by
    rw [← actual_feature π P k d j hj c]
    exact actual_feature_zero π P k d j hj c (by omega)
  rw [hzero,mul_zero]

def featureColumn (π : R) (P k D : ℕ) (i : FeatureBox H D k) (c : H → ℕ → R) : BaseMod R π P :=
  coeffMod R π P (rawFeature π k (fun e => (i.1 e).val) i.2 c)

def spanColumn (π : R) (P k D : ℕ) (a : FeatureBox H D k → R) (c : H → ℕ → R) : BaseMod R π P :=
  ∑ i : FeatureBox H D k, coeffMod R π P (a i)*featureColumn π P k D i c

theorem span_add (π : R) (P k D : ℕ) (a b : FeatureBox H D k → R) (c : H → ℕ → R) :
    spanColumn π P k D (a+b) c=spanColumn π P k D a c+spanColumn π P k D b c := by
  simp only [spanColumn,Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]

theorem monomialColumn (π : R) (P k D : ℕ) (a : ExponentBox H D)
    (g : R[X]) (c : H → ℕ → R) :
    spanColumn π P k D (fun b => if b.1=a then g.coeff (k-1-b.2.val) else 0) c =
      ∑ j : Fin k, coeffMod R π P (g.coeff (k-1-j.val))*
        coeffMod R π P (rawFeature π k (fun i => (a i).val) j c) := by
  unfold spanColumn
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _) (fun x _ hx => by simp [hx])]
  simp [featureColumn]

/-- Every actual centered A1 polynomial decoder has a uniform finite
coefficient vector on the entire digit chart. The same statement holds
without any characteristic restriction or input-by-input interpolation. -/
theorem source_in_finite_span (π : R) (P k : ℕ) (hp : 0<P) (hk : 0<k)
    (F : MvPolynomial H (Jet R k)) :
    ∃ a : FeatureBox H (P+k-2) k → R, ∀ c, topRead π P k F c=spanColumn π P k (P+k-2) a c := by
  induction F using MvPolynomial.induction_on' with
  | monomial d b =>
      obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective b
      by_cases hd : (∑ i : H,d i)≤P+k-2
      · let a : ExponentBox H (P+k-2) := fun i =>
          ⟨d i, by
            have h : d i ≤ ∑ j : H, d j := Finset.single_le_sum
              (f:=fun j : H => d j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            omega⟩
        refine ⟨fun b => if b.1=a then g.coeff (k-1-b.2.val) else 0,fun c => ?_⟩
        rw [monomialColumn π P k (P+k-2) a g c,topRead_monomial_sum π P k hk]
      · refine ⟨0,fun c => ?_⟩
        rw [monomial_over_degree_zero π P k hk d g c (by omega)]
        simp [spanColumn]
  | add F G hF hG =>
      obtain ⟨a,ha⟩ := hF
      obtain ⟨b,hb⟩ := hG
      exact ⟨a+b,fun c => by rw [topRead_add,ha,hb,span_add]⟩

def oneColumn (k D : ℕ) (i : FeatureBox H D k) (a : R) : MvPolynomial H (Jet R k) :=
  let d : H →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun e => (i.1 e).val)
  MvPolynomial.monomial d (AdjoinRoot.mk ((X:R[X])^k) (C a * X^(k-1-i.2.val)))

theorem oneColumn_exact (π : R) (P k D : ℕ) (hk : 0<k)
    (i : FeatureBox H D k) (a : R) (c : H → ℕ → R) :
    topRead π P k (oneColumn k D i a) c =
      coeffMod R π P a*featureColumn π P k D i c := by
  unfold oneColumn
  rw [topRead_monomial_mk π P k hk]
  simp only [Finsupp.equivFunOnFinite_symm_apply_toFun]
  rw [show (∏ e : H, shiftedPolynomial π k (c e)^(i.1 e).val : R[X]) *
        (C a * X^(k-1-i.2.val)) =
      C a*(X^(k-1-i.2.val)*(∏ e : H, shiftedPolynomial π k (c e)^(i.1 e).val : R[X]))
      by ac_rfl,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow_mul']
  have hh := i.2.isLt
  rw [if_pos (by omega),show k-1-(k-1-i.2.val)=i.2.val by omega,map_mul]
  rfl

theorem finite_span_in_source (π : R) (P k D : ℕ) (hk : 0<k)
    (a : FeatureBox H D k → R) :
    ∃ F : MvPolynomial H (Jet R k), ∀ c, topRead π P k F c=spanColumn π P k D a c := by
  refine ⟨∑ i : FeatureBox H D k, oneColumn k D i (a i),fun c => ?_⟩
  unfold spanColumn
  have hs : ∀ (s : Finset (FeatureBox H D k)), topRead π P k (∑ i ∈ s, oneColumn k D i (a i)) c =
      ∑ i ∈ s, coeffMod R π P (a i)*featureColumn π P k D i c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [topRead,coefficient]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi,Finset.sum_insert hi,topRead_add,ih,oneColumn_exact π P k D hk]
  exact hs Finset.univ

#print axioms topRead_add
#print axioms topRead_monomial_mk
#print axioms topRead_monomial_sum
#print axioms monomial_over_degree_zero
#print axioms source_in_finite_span
#print axioms oneColumn_exact
#print axioms finite_span_in_source
end
end V8CapacityFeatureSpan

