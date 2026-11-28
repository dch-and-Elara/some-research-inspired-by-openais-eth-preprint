import V8CapacityFeatureSpan
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Digit indeterminates of the actual projected features. Their total
degree is bounded before choosing the monic Newton basis. -/
namespace V8CapacitySymbolic
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityFeatures V8CapacityFeatureSpan V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000

variable {R H : Type*} [CommRing R] [Nontrivial R] [Fintype H]

abbrev Digits (H : Type*) (k : ℕ) := H × Fin k

def asInput {k : ℕ} (x : Digits H k → R) (i : H) (r : ℕ) : R :=
  if h : r<k then x (i,⟨r,h⟩) else 0

def symInput (k : ℕ) (i : H) (r : ℕ) : MvPolynomial (Digits H k) R :=
  if h : r<k then MvPolynomial.X (i,⟨r,h⟩) else 0

def feature (π : R) (k : ℕ) (α : H → ℕ) (j : ℕ) : MvPolynomial (Digits H k) R :=
  rawFeature (MvPolynomial.C π) k α j (symInput k)

variable {E : Type*}

def DegreeBound (n : ℕ) (p : (MvPolynomial E R)[X]) : Prop :=
  ∀ j, (p.coeff j).totalDegree≤n

theorem db_add {n : ℕ} {p q : (MvPolynomial E R)[X]}
    (hp : DegreeBound n p) (hq : DegreeBound n q) : DegreeBound n (p+q) := by
  intro j
  rw [Polynomial.coeff_add]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hp j) (hq j))

theorem db_const {n : ℕ} (p : MvPolynomial E R) (hp : p.totalDegree≤n) :
    DegreeBound n (C p) := by
  intro j
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hp
  · simp only [MvPolynomial.totalDegree_zero,Nat.zero_le]

theorem db_sum {I : Type*} {n : ℕ} (s : Finset I) (p : I → (MvPolynomial E R)[X])
    (h : ∀ i∈s, DegreeBound n (p i)) : DegreeBound n (∑ i ∈ s, p i) := by
  induction s using Finset.induction_on with
  | empty => intro j; simp only [Finset.sum_empty,Polynomial.coeff_zero,MvPolynomial.totalDegree_zero,Nat.zero_le]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact db_add (h i (Finset.mem_insert_self i s)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem db_mul {n m : ℕ} {p q : (MvPolynomial E R)[X]}
    (hp : DegreeBound n p) (hq : DegreeBound m q) : DegreeBound (n+m) (p*q) := by
  intro j
  rw [Polynomial.coeff_mul]
  have hh : ∀ a∈Finset.antidiagonal j, ((p.coeff a.1)*(q.coeff a.2)).totalDegree≤n+m :=
    fun a _ => (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hp _) (hq _))
  exact (MvPolynomial.totalDegree_finset_sum _ _).trans
    (Finset.sup_le hh)

theorem db_shift {n : ℕ} (p : (MvPolynomial E R)[X]) (i : ℕ) (hp : DegreeBound n p) :
    DegreeBound n (X^i*p) := by
  intro j
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs
  · exact hp _
  · simp only [MvPolynomial.totalDegree_zero,Nat.zero_le]

theorem db_pow {n : ℕ} {p : (MvPolynomial E R)[X]} (h : DegreeBound n p) (a : ℕ) :
    DegreeBound (a*n) (p^a) := by
  induction a with
  | zero =>
    rw [zero_mul,pow_zero,← map_one C]
    exact db_const _ (by simp only [MvPolynomial.totalDegree_one,Nat.zero_le])
  | succ a ih =>
    rw [Nat.succ_mul,pow_succ]
    exact db_mul ih h

theorem db_prod {J : Type*} (a : J → ℕ) (p : J → (MvPolynomial E R)[X])
    (s : Finset J) (h : ∀ i∈s, DegreeBound (a i) (p i)) :
    DegreeBound (∑ i ∈ s, a i) (∏ i ∈ s, p i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,Finset.prod_empty,← map_one C]
    exact db_const _ (by simp only [MvPolynomial.totalDegree_one,Nat.zero_le])
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    exact db_mul (h i (Finset.mem_insert_self i s)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem symInput_degree (k : ℕ) (i : H) (r : ℕ) : (symInput (R:=R) k i r).totalDegree≤1 := by
  unfold symInput
  split_ifs
  · rw [MvPolynomial.totalDegree_X]
  · simp

theorem db_symbolic (π : R) (k : ℕ) (i : H) :
    DegreeBound 1 (shiftedPolynomial (MvPolynomial.C π) k (symInput k i)) := by
  unfold shiftedPolynomial
  apply db_add
  · apply db_const
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simpa only [MvPolynomial.totalDegree_C,zero_add] using symInput_degree (R:=R) k i 0
  · nth_rw 1 [← pow_one (X:(MvPolynomial (Digits H k) R)[X])]
    apply db_shift
    apply db_sum
    intro r _
    rw [mul_comm]
    exact db_shift _ _ (db_const _ (symInput_degree (R:=R) k i (r+1)))

theorem feature_degree (π : R) (k : ℕ) (α : H → ℕ) (j : ℕ) :
    (feature π k α j).totalDegree≤∑ e : H, α e := by
  apply db_prod α _ Finset.univ (fun i _ => ?_) j
  simpa only [Nat.mul_one] using db_pow (db_symbolic π k i) (α i)

theorem feature_eval (π : R) (k : ℕ) (α : H → ℕ) (j : ℕ) (x : Digits H k → R) :
    MvPolynomial.eval x (feature π k α j) = rawFeature π k α j (asInput x) := by
  have hmap (i : H) :
      (shiftedPolynomial (MvPolynomial.C π) k (symInput (R:=R) k i)).map (MvPolynomial.eval x)
        = shiftedPolynomial π k (asInput x i) := by
    have hi (r : ℕ) : MvPolynomial.eval x (symInput (R:=R) k i r)=asInput x i r := by
      unfold symInput asInput
      split_ifs
      · exact MvPolynomial.eval_X _
      · exact map_zero _
    simp only [shiftedPolynomial,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
      Polynomial.map_sum,Polynomial.map_pow,map_mul,MvPolynomial.eval_C,hi]
  unfold feature rawFeature
  rw [← Polynomial.coeff_map]
  simp only [Polynomial.map_prod,Polynomial.map_pow,hmap]

#print axioms feature_degree
#print axioms feature_eval
end
end V8CapacitySymbolic

