import V9BitCost
import NativeInterpolation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Explicit coefficient-only interpolation for J8 and J9

This is the dense-ring arithmetic model, charged after the requested
samples have been acquired. Only two coefficients of each Lagrange
numerator are computed, with no materialization of the Vandermonde inverse.
-/

open scoped BigOperators Polynomial

namespace V9BitCostInterpolation

open Polynomial

section Recurrence

variable {R : Type*} [CommRing R]

structure LowState (R : Type*) where
  const : R
  linear : R
  denom : R

/-- Three products and three additions/negations for each factor:
constant, linear, and the denominator product at the distinguished node. -/
def factorStep (xi y : R) (s : LowState R) : LowState R :=
  ⟨-(s.const*y), s.const-s.linear*y, s.denom*(xi-y)⟩

def lowFactors (xi : R) : List R → LowState R
  | [] => ⟨1,0,1⟩
  | y::ys => factorStep xi y (lowFactors xi ys)

noncomputable def productFactors : List R → R[X]
  | [] => 1
  | y::ys => productFactors ys * (X-C y)

theorem productFactors_prod (ys : List R) :
    productFactors ys = (ys.map (fun y => (X:R[X])-C y)).prod := by
  induction ys with
  | nil => simp [productFactors]
  | cons y ys ih => simp [productFactors, ih, mul_comm]

/-- Exact low-coefficient recurrence, valid in the native quotient ring
with zero divisors. No rational-field hypothesis is used here. -/
theorem lowFactors_correct (xi : R) (ys : List R) :
    (lowFactors xi ys).const = (productFactors ys).coeff 0 ∧
      (lowFactors xi ys).linear = (productFactors ys).coeff 1 ∧
      (lowFactors xi ys).denom = (productFactors ys).eval xi := by
  induction ys with
  | nil => simp [lowFactors, productFactors, Polynomial.coeff_one]
  | cons y ys ih =>
    rcases ih with ⟨h₀,h₁,hd⟩
    rw [lowFactors, productFactors]
    change -( (lowFactors xi ys).const*y) = _ ∧
      (lowFactors xi ys).const-(lowFactors xi ys).linear*y = _ ∧
      (lowFactors xi ys).denom*(xi-y) = _
    rw [h₀, h₁, hd]
    simp [mul_sub, Polynomial.coeff_mul_C]

/-- Native low-state list, one entry for every other probe. -/
noncomputable def other {d : ℕ} (x : Fin (d+1) → R) (i : Fin (d+1)) : List R :=
  ((Finset.univ : Finset (Fin (d+1))).erase i).toList.map x

omit [CommRing R] in
theorem other_length {d : ℕ} (x : Fin (d+1) → R) (i : Fin (d+1)) :
    (other x i).length = d := by simp [other]

noncomputable def numerator {d : ℕ} (x : Fin (d+1) → R) (i : Fin (d+1)) : R[X] :=
  ∏ j ∈ (Finset.univ : Finset (Fin (d+1))).erase i, (X-C (x j))

theorem productFactors_other {d : ℕ} (x : Fin (d+1) → R) (i : Fin (d+1)) :
    productFactors (other x i) = numerator x i := by
  rw [productFactors_prod, other, List.map_map, Finset.prod_map_toList]
  rfl

theorem numerator_degree {d : ℕ} (x : Fin (d+1) → R) (i : Fin (d+1)) :
    (numerator x i).natDegree ≤ d := by
  let S : Finset (Fin (d+1)) := Finset.univ.erase i
  let g : Fin (d+1) → R[X] := fun j => X - C (x j)
  have hprod : (∏ j ∈ S, g j).natDegree ≤ ∑ j ∈ S, (g j).natDegree :=
    Polynomial.natDegree_prod_le S g
  have hsum : (∑ j ∈ S, (g j).natDegree) ≤ S.card := by
    calc
      _ ≤ ∑ _j ∈ S, (1 : ℕ) :=
        Finset.sum_le_sum (fun j _ => Polynomial.natDegree_X_sub_C_le (x j))
      _ = _ := by simp
  have hcard : S.card = d := by simp [S]
  exact hprod.trans (hsum.trans_eq hcard)

theorem numerator_off_diagonal {d : ℕ} (x : Fin (d+1) → R) {i j : Fin (d+1)}
    (h : j ≠ i) : (numerator x i).eval (x j) = 0 := by
  rw [numerator, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩) (by simp)

theorem numerator_unit_at_diagonal {d : ℕ} (x : Fin (d+1) → R)
    (hu : ∀ i j, i ≠ j → IsUnit (x j-x i)) (i : Fin (d+1)) :
    IsUnit ((lowFactors (x i) (other x i)).denom) := by
  rw [(lowFactors_correct (x i) (other x i)).2.2, productFactors_other,
    numerator, Polynomial.eval_prod]
  apply NativeInterpolation.unit_prod
  intro j hj
  simpa using hu j i (Finset.ne_of_mem_erase hj)

/-- The scalar formula actually evaluated after acquiring the samples.
The u_i are inverses of the accumulated unit denominators. -/
noncomputable def coefficientReadout {d : ℕ} (x samples inverses : Fin (d+1) → R) : R :=
  ∑ i, (samples i * inverses i) * (lowFactors (x i) (other x i)).linear

/-- Correctness of the coefficient-only readout against the native
evaluation semantics, even if the prescribed probes omit zero. -/
theorem coefficientReadout_eq {d : ℕ} (hd : 0 < d) (x : Fin (d+1) → R)
    (P : R[X]) (hP : P.natDegree ≤ d)
    (hu : ∀ i j, i ≠ j → IsUnit (x j-x i)) (inverses : Fin (d+1) → R)
    (hInv : ∀ i, (lowFactors (x i) (other x i)).denom * inverses i = 1) :
    coefficientReadout x (fun i => P.eval (x i)) inverses = P.coeff 1 := by
  let Q : R[X] := ∑ i, C (P.eval (x i) * inverses i) * numerator x i
  have hQ : Q.natDegree ≤ d :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ =>
      (Polynomial.natDegree_C_mul_le _ _).trans (numerator_degree x i))
  have hEval (j : Fin (d+1)) : Q.eval (x j) = P.eval (x j) := by
    have hi := hInv j
    rw [(lowFactors_correct (x j) (other x j)).2.2, productFactors_other, mul_comm] at hi
    simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [mul_assoc, hi, mul_one]
    · intro i _ hij
      rw [numerator_off_diagonal x hij.symm, mul_zero]
  have hdecode :
      (fun i : Fin (d+1) => Q.coeff i.val) = fun i : Fin (d+1) => P.coeff i.val := by
    calc
      _ = NativeInterpolation.decode x (fun i => Q.eval (x i)) :=
        (NativeInterpolation.decode_eval Q hQ x hu).symm
      _ = NativeInterpolation.decode x (fun i => P.eval (x i)) := by rw [funext hEval]
      _ = _ := NativeInterpolation.decode_eval P hP x hu
  have hone := congrFun hdecode (⟨1, by omega⟩ : Fin (d+1))
  rw [← hone]
  simp only [coefficientReadout, Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [(lowFactors_correct (x i) (other x i)).2.1, productFactors_other]

end Recurrence

section Inversion

/-- Horner recurrence for a geometric correction, using n multiplications
and n additions, regardless of zero divisors in the receiving ring. -/
def correction {R : Type*} [CommRing R] (a : R) : ℕ → R
  | 0 => 0
  | n+1 => 1+a*correction a n

theorem correction_identity {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    (1-a)*correction a n = 1-a^n := by
  induction n with
  | zero => simp [correction]
  | succ n ih =>
    rw [correction, pow_succ']
    calc
      _ = (1-a)+a*((1-a)*correction a n) := by ring
      _ = _ := by rw [ih]; ring

/-- The correction actually lifts an inverse from a mod-2 residue:
an explicit equality to 2 times a scalar is the only lift premise. -/
theorem inverse_from_residue {R : Type*} [CommRing R] (x b u : R) (p : ℕ)
    (h : 1-x*b = 2*u) (hp : (2:R)^p = 0) :
    x * (b*correction (1-x*b) p) = 1 := by
  have hn : (1-x*b)^p = 0 := by rw [h, mul_pow, hp, zero_mul]
  have hf := correction_identity (1-x*b) p
  rw [hn, sub_zero, sub_sub_cancel] at hf
  rw [← mul_assoc, hf]

/-- One square and one multiplication produce the next all-ones exponent.
This is the residue-field inverse algorithm for binary coordinates. -/
def allOnesPower {K : Type*} [GroupWithZero K] (x : K) : ℕ → K
  | 0 => 1
  | n+1 => (allOnesPower x n)^2*x

theorem allOnesPower_eq {K : Type*} [GroupWithZero K] (x : K) (n : ℕ) :
    allOnesPower x n = x^((2:ℕ)^n-1) := by
  induction n with
  | zero => simp [allOnesPower]
  | succ n ih =>
    rw [allOnesPower, ih, ← pow_mul, ← pow_succ]
    congr 1
    have hp := V9BitCost.modulus_pos n
    rw [pow_succ (2:ℕ)]
    omega

/-- The inverse seed in a field of size 2^e uses 2(e-1)+1 field
multiplications by the recurrence and the last squaring. -/
theorem residue_inverse_seed {K : Type*} [Field K] [Fintype K] (x : K) (hx : x ≠ 0)
    (e : ℕ) (he : 0 < e) (hc : Fintype.card K = (2:ℕ)^e) :
    ((allOnesPower x (e-1))^2)*x = 1 := by
  calc
    _ = allOnesPower x ((e-1)+1) := rfl
    _ = x^(Fintype.card K-1) := by
      rw [Nat.sub_add_cancel (by omega : 1≤e), allOnesPower_eq, hc]
    _ = 1 := FiniteField.pow_card_sub_one_eq_one x hx

end Inversion

/-- Dense ring operations per coefficient readout, with q native samples.
The formulas overcount (and may share) public coefficients. Acquiring the
sample values is not charged here. -/
def ringOps (q e p : ℕ) : ℕ := q*(6*(q-1)+2*e+2*p+12)

def postprocessEnvelope (m q e p : ℕ) : ℕ :=
  m * ringOps q e p * V9BitCost.ringMulEnvelope e p

/-- The direct data footprint is independent of the postprocessor's
ring-operation schedule. A binary address has e printed coordinates,
but a received scalar requires e words of p bits. -/
def receivedBits (m q e p : ℕ) : ℕ := m*q*e*p

theorem ringOps_le (q e p : ℕ) :
    ringOps q e p ≤ 12*q*(q+e+p+1) := by
  unfold ringOps
  have he : 6*(q-1)+2*e+2*p+12 ≤ 12*(q+e+p+1) := by omega
  calc
    _ ≤ q*(12*(q+e+p+1)) := Nat.mul_le_mul_left q he
    _ = _ := by ring

theorem postprocessEnvelope_le (m q e p : ℕ) :
    postprocessEnvelope m q e p ≤
      240*m*q*(q+e+p+1)*(e+1)^2*(p+1)^2 := by
  unfold postprocessEnvelope
  calc
    _ ≤ (m*(12*q*(q+e+p+1)))*(20*(e+1)^2*(p+1)^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left m (ringOps_le q e p)) (V9BitCost.ringMulEnvelope_le e p)
    _ = _ := by ring

#print axioms lowFactors_correct
#print axioms coefficientReadout_eq
#print axioms inverse_from_residue
#print axioms residue_inverse_seed
#print axioms postprocessEnvelope_le

end V9BitCostInterpolation

