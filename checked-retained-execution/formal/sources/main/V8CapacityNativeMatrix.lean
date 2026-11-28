import V8CapacityMonicBasis
import V8CapacityIntegrated

/-! The exact source feature matrix C of A2, including the ordinary
coefficient cut mu<P and the finite row set of total degree ≤ P+k-2. -/
namespace V8CapacityNativeMatrix
open scoped Classical BigOperators
open V8CapacityFeatures V8CapacityFeatureSpan V8CapacitySymbolic
open V8CapacityMonicBasis V8CapacityNewtonGrid V8CapacityFactorial
open V8CapacityCRTJet V8CapacityIntegrated

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {O H : Type*} [CommRing O] [IsDomain O] [Fintype H]
variable (π : O) (P k : ℕ)

abbrev DegreeCap (P k : ℕ) := P+k-2
abbrev Box (H : Type*) (P k : ℕ) := FeatureBox H (DegreeCap P k) k
abbrev Grid (H : Type*) [Fintype H] (P k : ℕ) := Row (Digits H k) (DegreeCap P k)

def α (i : Box H P k) : H → ℕ := fun e => (i.1 e).val

def symCol (i : Box H P k) : MvPolynomial (Digits H k) O :=
  if (∑ e : H, α P k i e)≤DegreeCap P k then feature π k (α P k i) i.2 else 0

theorem symCol_degree (i : Box H P k) : (symCol π P k i).totalDegree≤DegreeCap P k := by
  unfold symCol
  split_ifs with h
  · exact (feature_degree π k (α P k i) i.2).trans h
  · rw [MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _

/-- In a DVR this predicate is precisely mu(alpha,j)<P. An absent or
zero coefficient polynomial has no active place, in either characteristic. -/
def active (i : Box H P k) : Prop :=
  ∃ d : Digits H k →₀ ℕ, ¬π^P∣(symCol π P k i).coeff d

abbrev Columns (H : Type*) [Fintype H] (π : O) (P k : ℕ) :=
  {i : Box H P k // active π P k i}

theorem eval_dvd_of_coeff {E : Type*} (f : MvPolynomial E O) (x : E → O) (u : O)
    (h : ∀ d, u∣f.coeff d) : u∣MvPolynomial.eval x f := by
  conv_rhs => rw [f.as_sum]
  rw [map_sum]
  apply Finset.dvd_sum
  intro i _
  rw [MvPolynomial.eval_monomial]
  exact dvd_mul_of_dvd_left (h i) _

theorem inactive_zero (i : Box H P k) (hi : ¬active π P k i) (x : Digits H k → O) :
    coeffMod O π P (MvPolynomial.eval x (symCol π P k i))=0 := by
  unfold coeffMod
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Ideal.mem_span_singleton]
  exact eval_dvd_of_coeff (symCol π P k i) x _ (fun d => not_not.mp (fun hn => hi ⟨d,hn⟩))

theorem feature_column_eval (hP : 0<P) (hk : 0<k) (i : Box H P k) (x : Digits H k → O) :
    featureColumn π P k (DegreeCap P k) i (asInput x)=
      coeffMod O π P (MvPolynomial.eval x (symCol π P k i)) := by
  unfold symCol
  split_ifs with h
  · rw [feature_eval]
    rfl
  · rw [map_zero,map_zero]
    unfold featureColumn coeffMod
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.mem_span_singleton]
    have hi : i.2.val<k := i.2.isLt
    have he : P≤(∑ e : H, α P k i e)-i.2.val := by
      unfold DegreeCap at h
      omega
    exact (pow_dvd_pow π he).trans (feature_dvd π k (α P k i) i.2 (asInput x))

variable {q : ℕ} (D : V8CapacityDigits.Digits π q) (hq : 0<q)

theorem some_monic_coefficients (i : Columns H π P k) :
    ∃ a : Grid H P k → O, ∑ r : Grid H P k, a r • basisPoly D hq (rowDegree r) =
      symCol π P k i.val := by
  obtain ⟨a,ha⟩ := exact_monic_expansion (E:=Digits H k) D hq (DegreeCap P k)
    (symCol π P k i.val) (symCol_degree π P k i.val)
  refine ⟨a,?_⟩
  rw [← ha]
  apply Finset.sum_congr (by ext z; simp only [Finset.mem_univ])
  exact fun _ _ => rfl

def columnCoeffs (i : Columns H π P k) : Grid H P k → O :=
  Classical.choose (some_monic_coefficients π P k D hq i)

theorem column_expansion (i : Columns H π P k) :
    ∑ r : Grid H P k, columnCoeffs π P k D hq i r • basisPoly D hq (rowDegree r)=
      symCol π P k i.val :=
  Classical.choose_spec (some_monic_coefficients π P k D hq i)

def monicC : Matrix (Grid H P k) (Columns H π P k) O :=
  Matrix.of fun r i => columnCoeffs π P k D hq i r

theorem column_evaluates (i : Columns H π P k) (x : Digits H k → O) :
    MvPolynomial.eval x (symCol π P k i)=
      ∑ r : Grid H P k, tensor D hq (rowDegree r) x * monicC π P k D hq r i := by
  rw [← column_expansion π P k D hq i,map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,basis_eval,mul_comm]
  congr 1
  unfold tensor
  apply Finset.prod_congr rfl
  intro e _
  exact (Fin.prod_univ_eq_prod_range _ _).symm

theorem rawAt_is_active (w : Columns H π P k → O) (x : Digits H k → O) :
    rawAt D hq (rowDegree (E:=Digits H k) (n:=DegreeCap P k)) (monicC π P k D hq) w x =
      ∑ i : Columns H π P k, w i * MvPolynomial.eval x (symCol π P k i) := by
  unfold rawAt
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,column_evaluates π P k D hq,
    ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  ac_rfl

theorem padded_to_active (hP : 0<P) (hk : 0<k) (w : Box H P k → O) (x : Digits H k → O) :
    spanColumn π P k (DegreeCap P k) w (asInput x)=
      coeffMod O π P (rawAt D hq (rowDegree (E:=Digits H k) (n:=DegreeCap P k)) (monicC π P k D hq) (fun i => w i) x) := by
  unfold spanColumn
  simp only [rawAt_is_active π P k D hq,map_sum,map_mul,feature_column_eval π P k hP hk]
  let a := Finset.univ.filter (active π P k (H:=H))
  let f (i : Box H P k) :=
    coeffMod O π P (w i) * coeffMod O π P (MvPolynomial.eval x (symCol π P k i))
  change (∑ i : Box H P k, f i)=∑ i : Columns H π P k, f i
  rw [← Finset.sum_subtype a (by simp [a]) f]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hn
  have hi : ¬active π P k i := by
    intro hi
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  unfold f
  rw [inactive_zero π P k i hi, mul_zero]

/-- A faithful exact two-way bridge from the true centered jet decoder
to a coefficient vector of the anchored weighted Newton matrix. -/
theorem centered_source_iff [IsLocalRing O] (hP : 0<P) (hk : 0<k)
    (goal : (Digits H k → O) → BaseMod O π P) :
    (∃ F : MvPolynomial H (Jet O k), ∀ x, topRead π P k F (asInput x)=goal x) ↔
    (∃ w : Columns H π P k → O, ∀ x,
      coeffMod O π P (rawAt D hq (rowDegree (E:=Digits H k) (n:=DegreeCap P k)) (monicC π P k D hq) w x)=goal x) := by
  constructor
  · rintro ⟨F,hF⟩
    obtain ⟨a,ha⟩ := source_in_finite_span π P k hP hk F
    exact ⟨fun i => a i,fun x => (padded_to_active π P k D hq hP hk a x).symm.trans
      ((ha (asInput x)).symm.trans (hF x))⟩
  · rintro ⟨w,hw⟩
    let w' (i : Box H P k) := if h : active π P k i then w ⟨i,h⟩ else 0
    obtain ⟨F,hF⟩ := finite_span_in_source π P k (DegreeCap P k) hk w'
    refine ⟨F,fun x => ?_⟩
    rw [hF,padded_to_active π P k D hq hP hk]
    have he : (fun i : Columns H π P k => w' i)=w := by
      funext i
      exact dif_pos i.property
    rw [he,hw]

#print axioms symCol_degree
#print axioms eval_dvd_of_coeff
#print axioms inactive_zero
#print axioms feature_column_eval
#print axioms column_expansion
#print axioms column_evaluates
#print axioms rawAt_is_active
#print axioms padded_to_active
#print axioms centered_source_iff
end
end V8CapacityNativeMatrix

