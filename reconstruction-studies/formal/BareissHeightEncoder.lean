import BareissHeight
import AffineCostRows

/-!
The §4.2 evaluation-equation system for the actual binary encoder.
A row has one unknown for every nonconstant polynomial coefficient and one
for every measurement coefficient at each node. Local equations are zero
padding, so their index set can be the same for every output.
-/

namespace BareissHeight

open AffineEdge
open Polynomial
open scoped BigOperators Polynomial

abbrev Equation (q : ℕ) := Fin q × Word q
abbrev Unknown (q : ℕ) := (Word q × Fin (q-2)) ⊕ (Fin q × EncoderRow q)

/-- A computable entry of (5), using the same column classification as AffineCost. -/
def encoderAt {q : ℕ} (j : EncoderRow q) (v : Word q) : ℚ :=
  match AffineCost.scan v v with
  | .zero => encoderColumn v.1 none j
  | .one t => encoderColumn v.1 (some t) j
  | .two _ _ => 0

theorem encoderAt_eq {q : ℕ} (j : EncoderRow q) (v : Word q) :
    encoderAt j v = binaryEncoder q j v := (AffineCost.column_scan v j).symm

def constantEntry {q : ℕ} (u v : Word q) : ℚ := if u = v then 1 else 0

def encoderMatrix {q : ℕ} (sites : Fin q → ℚ) (u : Word q) :
    Matrix (Equation q) (Unknown q) ℚ :=
  Matrix.of fun (t,v) k =>
    if v.1 t = u.2 t then 0 else
      match k with
      | .inl (w,i) => if w = v then (sites t)^(i.val+1) else 0
      | .inr (s,j) => if s = t then -encoderAt j v else 0

def encoderRhs {q : ℕ} (u : Word q) (e : Equation q) : ℚ :=
  if e.2.1 e.1 = u.2 e.1 then 0 else -constantEntry u e.2

/-- The integer equation obtained by multiplying the node's rational equation
by the denominator of its label to degree q−2. -/
def encoderInt {q : ℕ} (sites : Fin q → ℚ) (u : Word q) :
    Matrix (Equation q) (Option (Unknown q)) ℤ :=
  Matrix.of fun (t,v) k =>
    if v.1 t = u.2 t then 0 else
      let d : ℤ := (sites t).den
      match k with
      | none => if u = v then -(d^(q-2)) else 0
      | some (.inl (w,i)) =>
          if w = v then (sites t).num^(i.val+1) * d^(q-2-(i.val+1)) else 0
      | some (.inr (s,j)) => if s = t then -(encoderAt j v).num * d^(q-2) else 0

private theorem den_mul_eq_num (x : ℚ) : (x.den : ℚ) * x = x.num := by
  have h := (div_eq_iff (by exact_mod_cast x.den_ne_zero : (x.den : ℚ) ≠ 0)).mp x.num_div_den
  simpa only [mul_comm (x.den : ℚ) x] using h.symm

private theorem encoder_num_cast {q : ℕ} (j : EncoderRow q) (v : Word q) :
    ((encoderAt j v).num : ℚ) = encoderAt j v := by
  rw [encoderAt_eq]
  rcases binaryEncoder_binary (F := ℚ) j v with h | h <;> simp [h]

theorem encoderInt_cast {q : ℕ} (sites : Fin q → ℚ) (u : Word q)
    (e : Equation q) (j : Option (Unknown q)) :
    (encoderInt sites u e j : ℚ) =
      (↑(sites e.1).den : ℚ)^(q-2) * augment (encoderMatrix sites u) (encoderRhs u) e j := by
  rcases e with ⟨t,v⟩
  by_cases hv : v.1 t = u.2 t
  · cases j <;> simp [encoderInt, augment, encoderMatrix, encoderRhs, hv]
  cases j with
  | none =>
    by_cases h : u = v <;> simp [encoderInt, augment, encoderRhs, constantEntry, hv, h]
  | some j =>
    rcases j with ⟨w,i⟩ | ⟨s,j⟩
    · by_cases h : w = v
      · have hi : i.val + 1 ≤ q-2 := i.isLt
        simp only [encoderInt, Matrix.of_apply, hv, if_false, h, if_true, augment, encoderMatrix,
          Option.elim'_some, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
        rw [← den_mul_eq_num, mul_pow]
        calc
          _ = ((sites t).den : ℚ)^(q-2-(i.val+1)) * ((sites t).den : ℚ)^(i.val+1) *
              (sites t)^(i.val+1) := by ring
          _ = _ := by rw [← pow_add, Nat.sub_add_cancel hi]
      · simp [encoderInt, augment, encoderMatrix, hv, h]
    · by_cases h : s = t <;>
        simp [encoderInt, augment, encoderMatrix, hv, h, encoder_num_cast, mul_comm]

theorem encoderInt_system_iff {q : ℕ} (sites : Fin q → ℚ) (u : Word q) (x : Unknown q → ℚ) :
    (∀ e, (∑ j, (encoderInt sites u e (some j) : ℚ) * x j) =
      (encoderInt sites u e none : ℚ)) ↔
      (∀ e, (∑ j, encoderMatrix sites u e j * x j) = encoderRhs u e) := by
  simp only [encoderInt_cast, augment, Matrix.of_apply, Option.elim'_some, Option.elim'_none,
    mul_assoc, ← Finset.mul_sum]
  apply forall_congr'
  intro e
  have hd : ((sites e.1).den : ℚ) ≠ 0 := by exact_mod_cast (sites e.1).den_ne_zero
  exact ⟨mul_left_cancel₀ (pow_ne_zero _ hd), congrArg (_ * ·)⟩

private theorem encoder_num_abs {q : ℕ} (j : EncoderRow q) (v : Word q) :
    (encoderAt j v).num.natAbs ≤ 1 := by
  rw [encoderAt_eq]
  rcases binaryEncoder_binary (F := ℚ) j v with h | h <;> simp [h]

/-- Every integer entry, including the right-hand side, has magnitude at
most 2^(b*(q−2)) given label numerators and denominators of magnitude ≤ 2^b. -/
theorem encoderInt_height {q b : ℕ} (sites : Fin q → ℚ) (u : Word q)
    (h : ∀ t, RatHeight b (sites t)) (e : Equation q) (j : Option (Unknown q)) :
    (encoderInt sites u e j).natAbs ≤ 2^(b*(q-2)) := by
  rcases e with ⟨t,v⟩
  have hpow (d : ℕ) : (sites t).den^d ≤ 2^(b*d) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (h t).2 _
  by_cases hv : v.1 t = u.2 t
  · simp [encoderInt, hv]
  cases j with
  | none =>
    by_cases hu : u = v
    · change (if v.1 t = u.2 t then 0 else if u = v then
          -((sites t).den : ℤ)^(q-2) else 0).natAbs ≤ _
      rw [if_neg hv, if_pos hu, Int.natAbs_neg, Int.natAbs_pow, Int.natAbs_natCast]
      exact hpow (q-2)
    · simp [encoderInt, hv, hu]
  | some j =>
    rcases j with ⟨w,i⟩ | ⟨s,j⟩
    · by_cases hw : w = v
      · have hi : i.val+1 ≤ q-2 := i.isLt
        simp only [encoderInt, Matrix.of_apply, hv, if_false, hw, if_true, Int.natAbs_mul,
          Int.natAbs_pow, Int.natAbs_natCast]
        calc
          _ ≤ (2^b)^(i.val+1) * (2^b)^(q-2-(i.val+1)) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (h t).1 _) (Nat.pow_le_pow_left (h t).2 _)
          _ = _ := by rw [← pow_add, Nat.add_comm (i.val+1), Nat.sub_add_cancel hi, pow_mul]
      · simp [encoderInt, hv, hw]
    · by_cases hs : s = t
      · simp only [encoderInt, Matrix.of_apply, hv, if_false, hs, if_true, Int.natAbs_mul,
          Int.natAbs_neg, Int.natAbs_pow, Int.natAbs_natCast]
        simpa only [one_mul] using Nat.mul_le_mul (encoder_num_abs j v) (hpow (q-2))
      · simp [encoderInt, hv, hs]

theorem encoderInt_minor_size {q b : ℕ} {K : Type*} [Fintype K] [DecidableEq K]
    (sites : Fin q → ℚ) (u : Word q) (h : ∀ t, RatHeight b (sites t))
    (r : K → Equation q) (c : K → Option (Unknown q)) :
    ((encoderInt sites u).submatrix r c).det.natAbs.size ≤
      Fintype.card K*(b*(q-2)+Fintype.card K)+1 :=
  minor_size_le (encoderInt sites u) r c (b*(q-2)) (encoderInt_height sites u h)

/-- The polynomial encoded by the nonconstant coordinates of a solution. -/
noncomputable def solutionPolynomial {q : ℕ} (u : Word q) (x : Unknown q → ℚ)
    (v : Word q) : ℚ[X] :=
  Polynomial.C (constantEntry u v) +
    ∑ i : Fin (q-2), Polynomial.C (x (.inl (v,i))) * X^(i.val+1)

private theorem rationalRow_sum {q : ℕ} (sites : Fin q → ℚ) (u v : Word q) (t : Fin q)
    (h : v.1 t ≠ u.2 t) (x : Unknown q → ℚ) :
    (∑ k, encoderMatrix sites u (t,v) k * x k) =
      (∑ i : Fin (q-2), x (.inl (v,i)) * (sites t)^(i.val+1)) -
        ∑ j : EncoderRow q, x (.inr (t,j)) * binaryEncoder q j v := by
  simp only [encoderMatrix, Matrix.of_apply, h, if_false, Fintype.sum_sum_type, Fintype.sum_prod_type,
    ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg, encoderAt_eq, mul_comm]

theorem encoderMatrix_system_iff {q : ℕ} (sites : Fin q → ℚ) (u : Word q) (x : Unknown q → ℚ) :
    (∀ e, (∑ j, encoderMatrix sites u e j * x j) = encoderRhs u e) ↔
      (∀ t v, v.1 t ≠ u.2 t →
        (solutionPolynomial u x v).eval (sites t) =
          ∑ j : EncoderRow q, x (.inr (t,j)) * binaryEncoder q j v) := by
  have evalP (t : Fin q) (v : Word q) :
      (solutionPolynomial u x v).eval (sites t) =
        constantEntry u v + ∑ i : Fin (q-2), x (.inl (v,i)) * (sites t)^(i.val+1) := by
    simp [solutionPolynomial, eval_finset_sum]
  constructor
  · intro hs t v hv
    have he := hs (t,v)
    rw [rationalRow_sum sites u v t hv x] at he
    simp only [encoderRhs, hv, if_false] at he
    rw [evalP]
    linarith only [he]
  · rintro hs ⟨t,v⟩
    by_cases hv : v.1 t = u.2 t
    · simp [encoderMatrix, encoderRhs, hv]
    · have he := hs t v hv
      rw [evalP] at he
      rw [rationalRow_sum sites u v t hv x]
      simp only [encoderRhs, hv, if_false]
      linarith only [he]

/-- The matrices are consistent for the paper's distinct nonzero rational labels. -/
theorem encoderInt_consistent {q : ℕ} (sites : Fin q → ℚ) (u : Word q)
    (hq : 2 ≤ q) (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    ∃ x : Unknown q → ℚ, ∀ e, (∑ j, (encoderInt sites u e (some j) : ℚ) * x j) =
      (encoderInt sites u e none : ℚ) := by
  obtain ⟨⟨P,hP⟩, _⟩ := binaryEncoder_attains sites hq hi hn
  obtain ⟨c₀,c₁,L,hL⟩ := rowSystem_of_affine (affine_test_of_paired hq hi hP) u
  let p := reconstructEntry sites (binaryEncoder q) c₀ c₁ L
  let scale (t : Fin q) := (-(∏ s, -sites s))⁻¹ * (sites t)^(q-1)
  let x : Unknown q → ℚ := Sum.elim
    (fun p' => (p p'.1).coeff (p'.2.val+1))
    (fun p' => c₀ p'.2 + scale p'.1 * c₁ p'.2)
  refine ⟨x, (encoderInt_system_iff sites u x).mpr ((encoderMatrix_system_iff sites u x).mpr ?_)⟩
  intro t v hv
  have he : (solutionPolynomial u x v).eval (sites t) = (p v).eval (sites t) := by
    have hd : (p v).natDegree < q-2+1 := Nat.lt_succ_of_le (reconstructEntry_degree hq hL v)
    rw [Polynomial.eval_eq_sum_range' hd, Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range]
    have hz : (p v).coeff 0 = constantEntry u v := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact reconstructEntry_zero hq hn hL v
    simp [solutionPolynomial, x, eval_finset_sum, hz, add_comm]
  rw [he, show (p v).eval (sites t) = (∑ j, c₀ j * binaryEncoder q j v) +
    scale t * ∑ j, c₁ j * binaryEncoder q j v from reconstructEntry_local hL t v hv]
  simp only [x, Sum.elim_inr, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Solutions of the actual integer systems yield a recovery matrix. -/
theorem paired_of_encoderInt_solutions {q : ℕ} (sites : Fin q → ℚ)
    (x : Word q → Unknown q → ℚ)
    (h : ∀ u e, (∑ j, (encoderInt sites u e (some j) : ℚ) * x u j) =
      (encoderInt sites u e none : ℚ)) :
    PairedCondition sites (binaryEncoder q) (q-2) (fun u => solutionPolynomial u (x u)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    apply (natDegree_add_le _ _).trans
    refine max_le (by simp) ?_
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le _ _).trans (by simpa only [natDegree_X_pow] using Nat.succ_le_of_lt i.isLt)
  · intro u v
    by_cases hv : u = v <;> simp [solutionPolynomial, eval_finset_sum, constantEntry, hv]
  · intro u t z hk hl
    have he := (encoderMatrix_system_iff sites u (x u)).mp
      ((encoderInt_system_iff sites u (x u)).mp (h u))
    have hterm (v : Word q) :
        (solutionPolynomial u (x u) v).eval (sites t) * z v =
          (∑ j : EncoderRow q, x u (.inr (t,j)) * binaryEncoder q j v) * z v := by
      by_cases hv : v.1 t = u.2 t
      · simp [hl v hv]
      · rw [he t v hv]
    simp only [hterm, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hk, mul_zero, Finset.sum_const_zero]

end BareissHeight
