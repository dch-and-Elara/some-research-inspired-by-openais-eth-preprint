import BooleanCube.Splines

namespace LocalReconstruction
open Polynomial
open scoped Polynomial
noncomputable section

def EqualEdges {q : ℕ} (a : Fin q → ℚ) (f : Cube q → ℚ[X]) : Prop :=
  ∀ i x, (f x).eval (a i) = (f (flip i x)).eval (a i)

/-- The second test family may take arbitrary values on deleted vertices. -/
theorem bilinear_certificate {q d j l : ℕ} {a : Fin q → ℚ} (ha : Function.Injective a)
    {A : Set (Cube q)} {p h g : Cube q → ℚ[X]} (hp : edgeCondition a A d p)
    (hh : EqualEdges a h) (hg : EqualEdges a g) (hz : ∀ x ∈ A, h x = 0)
    (hj : ∀ x, (h x).natDegree ≤ j) (hl : ∀ x, (g x).natDegree ≤ l)
    (hd : d+j+l < q) : ∑ x, (h x).eval 0 * (g x).eval 0 = 0 := by
  classical
  let F : ℚ[X] := ∑ x, p x * h x * g x
  have bound : F.natDegree ≤ d+j+l := by
    apply natDegree_sum_le_of_forall_le
    intro x _
    exact natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add (hp.1 x) (hj x))) (hl x))
  have roots (i : Fin q) : F.eval (a i) = 0 := by
    let v := fun x => (p x).eval (a i) * (h x).eval (a i) * (g x).eval (a i)
    have e (x : Cube q) : v x + v (flip i x) = 0 := by
      dsimp only [v]
      rw [← hh i x, ← hg i x, ← add_mul, ← add_mul]
      by_cases hx : x ∈ A
      · simp [hz x hx]
      by_cases hy : flip i x ∈ A
      · rw [hh i x,hz _ hy]; simp
      · rw [hp.2.2 i x hx hy]; simp
    have t := (flipEquiv i).sum_comp v
    change (∑ x, v (flip i x)) = ∑ x, v x at t
    have z : (∑ x, v x) + (∑ x, v (flip i x)) = 0 := by
      rw [← Finset.sum_add_distrib]; simp [e]
    rw [t] at z
    have zz : ∑ x, v x = 0 := by linarith
    simpa only [F,eval_finset_sum,eval_mul,v] using zz
  have zero := eq_zero_of_natDegree_lt_card_of_eval_eq_zero F ha roots
    (by simpa using bound.trans_lt hd)
  have e := congrArg (Polynomial.eval (0:ℚ)) zero
  simpa only [F,eval_finset_sum,eval_mul,hp.2.1,one_mul,eval_zero] using e

theorem square_obstruction {q d k : ℕ} {a : Fin q → ℚ} (ha : Function.Injective a)
    (hn : ∀ i, a i ≠ 0) {A : Set (Cube q)} {p : Cube q → ℚ[X]} (hp : edgeCondition a A d p)
    (hd : d+2*k < q) {h : Cube q → ℚ[X]} (hh : EqualEdges a h)
    (hz : ∀ x ∈ A, h x = 0) (hk : ∀ x, (h x).natDegree ≤ k) : ∀ x, h x = 0 := by
  induction k generalizing h with
  | zero =>
    have e := bilinear_certificate ha hp hh hh hz hk hk (by omega)
    intro x
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg ((h x).eval 0))).mp e
      x (Finset.mem_univ _)
    have z : (h x).coeff 0 = 0 := by simpa only [coeff_zero_eq_eval_zero] using (mul_self_eq_zero.mp he)
    rw [eq_C_of_natDegree_le_zero (hk x),z,C_0]
  | succ k ih =>
    have e := bilinear_certificate ha hp hh hh hz hk hk (by omega)
    have h0 (x : Cube q) : (h x).coeff 0 = 0 := by
      have he := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg ((h x).eval 0))).mp e
        x (Finset.mem_univ _)
      simpa only [coeff_zero_eq_eval_zero] using (mul_self_eq_zero.mp he)
    have hx (x : Cube q) : X * (h x).divX = h x := by simpa [h0] using X_mul_divX_add (h x)
    have compat : EqualEdges a (fun x => (h x).divX) := by
      intro i x
      apply mul_left_cancel₀ (hn i)
      have e := hh i x
      rw [← hx x, ← hx (flip i x),eval_mul,eval_mul,eval_X] at e
      exact e
    have z := ih (by omega) compat (fun x hx => by simp [hz x hx])
      (fun x => by rw [natDegree_divX_eq_natDegree_tsub_one]; have := hk x; omega)
    intro x
    rw [← hx x,z x,mul_zero]

theorem square_budget {q d k : ℕ} {a : Fin q → ℚ} (ha : Function.Injective a)
    (hn : ∀ i, a i ≠ 0) (A : Finset (Cube q)) {p : Cube q → ℚ[X]}
    (hp : edgeCondition a (↑A) d p) (hd : d+2*k < q) :
    (∑ j ∈ Finset.range (q+1), (k+1-j) * q.choose j) ≤ (k+1)*A.card := by
  classical
  let T : splines a k →ₗ[ℚ] (↥A → Bounded (k+1)) :=
    LinearMap.pi fun x => (LinearMap.proj (R := ℚ) x.val).comp (splines a k).subtype
  have inj : Function.Injective T := by
    intro u v heq
    let f := u-v
    have hf : T f = 0 := by
      funext x
      exact sub_eq_zero.mpr (congrFun heq x)
    have z := square_obstruction ha hn hp hd (h := fun x => (f.val x).val) f.property
      (fun x hx => congrArg Subtype.val (congrFun hf (⟨x,hx⟩ : ↥A))) (fun x => by
        have hdeg := mem_degreeLT.mp (f.val x).property
        by_cases he : (f.val x).val = 0
        · simp [he]
        rw [degree_eq_natDegree he] at hdeg
        exact Nat.le_of_lt_succ (WithBot.coe_lt_coe.mp hdeg))
    exact sub_eq_zero.mp (show f = 0 from Subtype.ext (funext fun x => Subtype.ext (z x)))
  have hdim := LinearMap.finrank_le_finrank_of_injective inj
  rw [spline_dimension ha,Module.finrank_pi_fintype] at hdim
  have he : Module.finrank ℚ (Bounded (k+1)) = k+1 := by
    simpa using (degreeLTEquiv ℚ (k+1)).finrank_eq
  simpa [he,Nat.mul_comm] using hdim

end
end LocalReconstruction
