import BooleanCube.Asymmetric

namespace LocalReconstruction
open Polynomial
open scoped Polynomial
noncomputable section

/-- At label i the vector is supported on the zero half of coordinate i. -/
def zeroHalfTests {q : ℕ} (a : Fin q → ℚ) (h : Cube q → ℚ[X]) : Prop :=
  ∀ i x, x i = true → (h x).eval (a i) = 0

private def measured {q m : ℕ} (M : Matrix (Fin m) (Cube q) ℚ)
    (h : Cube q → ℚ[X]) (i : Fin m) : ℚ[X] := ∑ x, C (M i x) * h x

/-- A bilinear certificate in the original input coordinates.
Only the right input is annihilated by the shared measurements. -/
theorem matrix_bilinear_certificate {q m d j l : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) {M : Matrix (Fin m) (Cube q) ℚ} {P}
    (hp : matrixCondition a M d P) {h g : Cube q → ℚ[X]}
    (hh : zeroHalfTests a h) (hg : zeroHalfTests a g)
    (hz : ∀ i, (∑ x, C (M i x) * h x) = 0)
    (hj : ∀ x, (h x).natDegree ≤ j) (hl : ∀ x, (g x).natDegree ≤ l)
    (hd : d+j+l < q) : ∑ x, (h x).eval 0 * (g x).eval 0 = 0 := by
  classical
  let F : ℚ[X] := ∑ u, (∑ v, P u v * h v) * g u
  have bound : F.natDegree ≤ d+j+l := by
    apply natDegree_sum_le_of_forall_le
    intro u _
    apply natDegree_mul_le.trans (Nat.add_le_add _ (hl u))
    apply natDegree_sum_le_of_forall_le
    intro v _
    exact natDegree_mul_le.trans (Nat.add_le_add (hp.1 u v) (hj v))
  have roots (i : Fin q) : F.eval (a i) = 0 := by
    have row : rowTest M (fun x => (h x).eval (a i)) := by
      intro t
      simpa only [eval_finset_sum,eval_mul,eval_C,eval_zero] using congrArg (eval (a i)) (hz t)
    simp only [F,eval_finset_sum,eval_mul]
    apply Finset.sum_eq_zero
    intro u _
    cases hu : u i with
    | true => simp [hg i u hu]
    | false =>
      apply mul_eq_zero_of_left
      apply hp.2.2 u i _ row
      intro x ne
      apply hh i x
      cases hx : x i <;> simp_all
  have z := eq_zero_of_natDegree_lt_card_of_eval_eq_zero F ha roots
    (by simpa using bound.trans_lt hd)
  have ev := congrArg (eval (0:ℚ)) z
  simpa [F,eval_finset_sum,hp.2.1,ite_mul] using ev

/-- At degree d + 2k < q the only zero-half test in the polynomial kernel is zero. -/
theorem matrix_square_obstruction {q m d k : ℕ} {a : Fin q → ℚ} (ha : Function.Injective a)
    (hn : ∀ i, a i ≠ 0) {M : Matrix (Fin m) (Cube q) ℚ} {P}
    (hp : matrixCondition a M d P) (hd : d+2*k < q) {h : Cube q → ℚ[X]}
    (hh : zeroHalfTests a h) (hz : ∀ i, (∑ x, C (M i x) * h x) = 0)
    (hk : ∀ x, (h x).natDegree ≤ k) : ∀ x, h x = 0 := by
  induction k generalizing h with
  | zero =>
    have e := matrix_bilinear_certificate ha hp hh hh hz hk hk (by omega)
    intro x
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg ((h x).eval 0))).mp e
      x (Finset.mem_univ _)
    have z : (h x).coeff 0 = 0 := by simpa only [coeff_zero_eq_eval_zero] using (mul_self_eq_zero.mp he)
    rw [eq_C_of_natDegree_le_zero (hk x),z,C_0]
  | succ k ih =>
    have e := matrix_bilinear_certificate ha hp hh hh hz hk hk (by omega)
    have h0 (x : Cube q) : (h x).coeff 0 = 0 := by
      have he := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg ((h x).eval 0))).mp e
        x (Finset.mem_univ _)
      simpa only [coeff_zero_eq_eval_zero] using (mul_self_eq_zero.mp he)
    have hx (x : Cube q) : X * (h x).divX = h x := by simpa [h0] using X_mul_divX_add (h x)
    have compat : zeroHalfTests a (fun x => (h x).divX) := by
      intro i x hbit
      have e := hh i x hbit
      rw [← hx x,eval_mul,eval_X] at e
      exact (mul_eq_zero.mp e).resolve_left (hn i)
    have kernel (i : Fin m) : (∑ x, C (M i x) * (h x).divX) = 0 := by
      apply (mul_eq_zero.mp _).resolve_left X_ne_zero
      rw [← hz i,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_left_comm,hx]
    have z := ih (by omega) compat kernel
      (fun x => by rw [natDegree_divX_eq_natDegree_tsub_one]; have := hk x; omega)
    intro x
    rw [← hx x,z x,mul_zero]

private def testMode {q : ℕ} (a : Fin q → ℚ) (s x : Cube q) : ℚ[X] :=
  C (if x = s then (1:ℚ) else 0) * ∏ i ∈ ones s, (1 - C (a i)⁻¹ * X)

private theorem mode_zero {q : ℕ} (a : Fin q → ℚ) (s x : Cube q) :
    (testMode a s x).eval 0 = if x = s then 1 else 0 := by
  by_cases e : x = s <;> simp [testMode,e,eval_prod]

private theorem mode_degree {q : ℕ} (a : Fin q → ℚ) (s x : Cube q) :
    (testMode a s x).natDegree ≤ weight s := by
  apply (natDegree_C_mul_le ..).trans
  apply (natDegree_prod_le ..).trans
  calc
    _ ≤ ∑ _i ∈ ones s, 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (natDegree_sub_le ..).trans
      exact max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp))
    _ = weight s := by simp [weight]

private theorem mode_support {q : ℕ} {a : Fin q → ℚ} (hn : ∀ i, a i ≠ 0) (s : Cube q) :
    zeroHalfTests a (testMode a s) := by
  intro i x hx
  by_cases e : x = s
  · subst x
    have hi : i ∈ ones s := by simp [ones,hx]
    simp only [testMode,eval_mul,eval_C,eval_prod]
    rw [Finset.prod_eq_zero hi (by simp [hn i]),mul_zero]
  · simp [testMode,e]

private abbrev Slot (q r K : ℕ) :=
  {u : Fin (K+1) × Cube q // weight u.2 ≤ min u.1.val (r-u.1.val)}

private def pack {q r K : ℕ} (a : Fin q → ℚ) (J : ℕ) (c : Slot q r K → ℚ)
    (x : Cube q) : ℚ[X] :=
  ∑ u, if u.val.1.val ≤ J then C (c u) * (X^(J-u.val.1.val) * testMode a u.val.2 x) else 0

private theorem pack_degree {q r K : ℕ} (a : Fin q → ℚ) (J : ℕ) (c : Slot q r K → ℚ)
    (x : Cube q) : (pack a J c x).natDegree ≤ J := by
  apply natDegree_sum_le_of_forall_le
  intro u _
  split_ifs with hu
  · apply (natDegree_C_mul_le ..).trans
    apply natDegree_mul_le.trans
    rw [natDegree_X_pow]
    have h := (mode_degree a u.val.2 x).trans (u.property.trans (min_le_left ..))
    omega
  · simp

private theorem pack_support {q r K : ℕ} {a : Fin q → ℚ} (hn : ∀ i, a i ≠ 0)
    (J : ℕ) (c : Slot q r K → ℚ) : zeroHalfTests a (pack a J c) := by
  intro i x hx
  simp only [pack,eval_finset_sum]
  apply Finset.sum_eq_zero
  intro u _
  split_ifs <;> simp [mode_support hn u.val.2 i x hx]

private theorem pack_measured_injective {q m d r K : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0)
    {M : Matrix (Fin m) (Cube q) ℚ} {P} (hp : matrixCondition a M d P) (hr : d+r < q)
    (c : Slot q r K → ℚ) (hzero : ∀ i, measured M (pack a K c) i = 0) (hK : K ≤ r) : c = 0 := by
  classical
  by_contra hc
  let I := Finset.univ.filter (fun u => c u ≠ 0)
  have hi : I.Nonempty := by
    by_contra! h
    apply hc
    funext u
    by_contra ne
    have : u ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne⟩
    simp [h] at this
  obtain ⟨w,hw,hm⟩ := I.exists_max_image (fun u => u.val.1.val) hi
  let J := w.val.1.val
  have hJK : J ≤ K := Nat.le_of_lt_succ w.val.1.isLt
  have cut (u : Slot q r K) (h : ¬u.val.1.val ≤ J) : c u = 0 := by
    by_contra ne
    exact h (hm u (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne⟩))
  have fact (x : Cube q) : X^(K-J) * pack a J c x = pack a K c x := by
    simp only [pack,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [if_pos (Nat.le_of_lt_succ u.val.1.isLt)]
    by_cases h : u.val.1.val ≤ J
    · rw [if_pos h,show K-u.val.1.val = K-J+(J-u.val.1.val) by omega,pow_add]
      ring
    · simp [h,cut u h]
  have vanish (i : Fin m) : measured M (pack a J c) i = 0 := by
    apply (mul_eq_zero.mp _).resolve_left (pow_ne_zero (K-J) X_ne_zero)
    rw [← hzero i]
    unfold measured
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← fact x]
    ring
  have wdeg := w.property.trans (min_le_right ..)
  have orth := matrix_bilinear_certificate ha hp (pack_support hn J c) (mode_support hn w.val.2)
    vanish (pack_degree a J c) (fun x => (mode_degree a w.val.2 x).trans wdeg)
    (by dsimp [J] at *; omega)
  simp only [mode_zero,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] at orth
  have value : (pack a J c w.val.2).eval 0 = c w := by
    simp only [pack,eval_finset_sum]
    rw [Finset.sum_eq_single w]
    · simp [J,mode_zero]
    · intro u _ ne
      by_cases e : u.val.1.val = J
      · have hs : w.val.2 ≠ u.val.2 := fun h => ne (Subtype.ext (Prod.ext (Fin.ext e) h.symm))
        simp [e,mode_zero,hs]
      · by_cases le : u.val.1.val ≤ J
        · have diff : J-u.val.1.val ≠ 0 := by omega
          simp [le,diff]
        · simp [le]
    · simp
  exact (Finset.mem_filter.mp hw).2 (value.symm.trans orth)

/-- Finite bilinear row-count bound for arbitrary rational measurements. -/
theorem matrix_bilinear_budget {q m d r K : ℕ} {a : Fin q → ℚ} (ha : Function.Injective a)
    (hn : ∀ i, a i ≠ 0) {M : Matrix (Fin m) (Cube q) ℚ} {P}
    (hp : matrixCondition a M d P) (hr : d+r < q) (hK : K ≤ r) :
    (∑ j ∈ Finset.range (K+1), ∑ l ∈ Finset.range (min j (r-j)+1), q.choose l) ≤
      (K+1)*m := by
  classical
  have degree (c : Slot q r K → ℚ) (i : Fin m) : (measured M (pack a K c) i).natDegree ≤ K := by
    apply natDegree_sum_le_of_forall_le
    intro x _
    exact (natDegree_C_mul_le ..).trans (pack_degree a K c x)
  let T : (Slot q r K → ℚ) →ₗ[ℚ] (Fin m → Bounded (K+1)) :=
    { toFun := fun c i => ⟨measured M (pack a K c) i, mem_degreeLT.mpr
        (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (degree c i))))⟩
      map_add' := by
        intro c b; funext i; apply Subtype.ext
        change measured M (pack a K (c+b)) i = measured M (pack a K c) i + measured M (pack a K b) i
        simp only [measured,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← mul_add]
        congr 1
        simp only [pack,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        simp [Nat.le_of_lt_succ u.val.1.isLt,add_mul]
      map_smul' := by
        intro z c; funext i; apply Subtype.ext
        change measured M (pack a K (z • c)) i = z • measured M (pack a K c) i
        simp only [measured,Finset.smul_sum,smul_eq_C_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_left_comm]
        congr 1
        simp only [pack,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        simp [Nat.le_of_lt_succ u.val.1.isLt,mul_assoc] }
  have hT : Function.Injective T := by
    intro u v e
    apply sub_eq_zero.mp
    apply pack_measured_injective ha hn hp hr _ _ hK
    intro i
    have : T (u-v) = 0 := by rw [T.map_sub,e,sub_self]
    exact congrArg Subtype.val (congrFun this i)
  have dim := LinearMap.finrank_le_finrank_of_injective hT
  rw [Module.finrank_pi, Module.finrank_pi_fintype] at dim
  have he : Module.finrank ℚ (Bounded (K+1)) = K+1 := by
    simpa using (degreeLTEquiv ℚ (K+1)).finrank_eq
  have eq (m : ℕ) : Fintype.card {s : Cube q // weight s ≤ m} =
      ∑ l ∈ Finset.range (m+1), q.choose l := by
    rw [Fintype.subtype_card]
    simp_rw [← layer_size]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext x
    simp
  let E : Slot q r K ≃ ((j : Fin (K+1)) × {s : Cube q // weight s ≤ min j.val (r-j.val)}) :=
    { toFun := fun u => ⟨u.val.1,u.val.2,u.property⟩
      invFun := fun u => ⟨(u.1,u.2.val),u.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr E,Fintype.card_sigma] at dim
  simp_rw [eq] at dim
  rw [Fin.sum_univ_eq_sum_range (fun j => ∑ l ∈ Finset.range (min j (r-j)+1), q.choose l) (K+1)] at dim
  simpa [he,Nat.mul_comm] using dim

end
end LocalReconstruction
