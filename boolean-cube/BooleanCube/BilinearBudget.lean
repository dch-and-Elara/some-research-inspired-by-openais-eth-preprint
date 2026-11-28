import BooleanCube.Certificates

namespace LocalReconstruction
open Polynomial
open scoped Polynomial
noncomputable section

private def testMode {q : ℕ} (a : Fin q → ℚ) (s x : Cube q) : ℚ[X] :=
  C (walsh x s) * ∏ i ∈ ones s, (1 - C (a i)⁻¹ * X)

private theorem mode_zero {q : ℕ} (a : Fin q → ℚ) (s x : Cube q) :
    (testMode a s x).eval 0 = walsh x s := by simp [testMode,eval_prod]

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

private theorem mode_edges {q : ℕ} {a : Fin q → ℚ} (hn : ∀ i, a i ≠ 0) (s : Cube q) :
    EqualEdges a (testMode a s) := by
  intro i x
  simp only [testMode,eval_mul,eval_C,eval_prod,walsh_flip]
  cases hs : s i with
  | false => simp [signBit]
  | true =>
    have hi : i ∈ ones s := by simp [ones,hs]
    have z : (∏ t ∈ ones s, eval (a i) (1 - C (a t)⁻¹ * X)) = 0 :=
      Finset.prod_eq_zero hi (by simp [hn i])
    simp only [z,mul_zero]

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

private theorem pack_edges {q r K : ℕ} {a : Fin q → ℚ} (hn : ∀ i, a i ≠ 0)
    (J : ℕ) (c : Slot q r K → ℚ) : EqualEdges a (pack a J c) := by
  intro i x
  simp only [pack,eval_finset_sum]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> simp only [eval_mul,mode_edges hn u.val.2 i x]

private theorem pack_restrict_injective {q d r K : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) {A : Finset (Cube q)}
    {p : Cube q → ℚ[X]} (hp : edgeCondition a ↑A d p) (hr : d+r < q)
    (c : Slot q r K → ℚ) (hzero : ∀ x ∈ A, pack a K c x = 0) (hK : K ≤ r) : c = 0 := by
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
  have vanish (x : Cube q) (hx : x ∈ A) : pack a J c x = 0 :=
    (mul_eq_zero.mp ((fact x).trans (hzero x hx))).resolve_left (pow_ne_zero _ X_ne_zero)
  have wdeg := w.property.trans (min_le_right ..)
  have orth := bilinear_certificate ha hp (pack_edges hn J c) (mode_edges hn w.val.2)
    vanish (pack_degree a J c) (fun x => (mode_degree a w.val.2 x).trans wdeg)
    (by dsimp [J] at *; omega)
  have ev (x : Cube q) : (pack a J c x).eval 0 =
      ∑ u, if u.val.1.val = J then c u * walsh x u.val.2 else 0 := by
    simp only [pack,eval_finset_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases eq : u.val.1.val = J
    · simp [eq,mode_zero]
    by_cases le : u.val.1.val ≤ J
    · have ne : J-u.val.1.val ≠ 0 := by omega
      simp [le,eq,ne,mode_zero]
    · simp [le,eq]
  simp_rw [ev,mode_zero,Finset.sum_mul] at orth
  rw [Finset.sum_comm] at orth
  have calcTerm (u : Slot q r K) :
      (∑ x : Cube q, (if u.val.1.val = J then c u * walsh x u.val.2 else 0) * walsh x w.val.2)
      = if u = w then c w * (2:ℚ)^q else 0 := by
    have ho : (∑ x, walsh x u.val.2 * walsh x w.val.2) =
        if u.val.2 = w.val.2 then (2:ℚ)^q else 0 := by
      simpa only [walsh_comm _ u.val.2, walsh_comm _ w.val.2] using walsh_orthogonal u.val.2 w.val.2
    by_cases he : u = w
    · subst u
      simp only [J, if_true, mul_assoc,← Finset.mul_sum,ho]
    by_cases hj : u.val.1.val = J
    · have hs : u.val.2 ≠ w.val.2 := fun hh => he (Subtype.ext (Prod.ext (Fin.ext hj) hh))
      simp only [if_pos hj,if_neg he,mul_assoc,← Finset.mul_sum,ho,if_neg hs,mul_zero]
    · simp [hj,he]
  simp_rw [calcTerm] at orth
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at orth
  exact (Finset.mem_filter.mp hw).2 ((mul_eq_zero.mp orth).resolve_right (by positivity))

theorem bilinear_budget {q d r K : ℕ} {a : Fin q → ℚ} (ha : Function.Injective a)
    (hn : ∀ i, a i ≠ 0) (A : Finset (Cube q)) {p : Cube q → ℚ[X]}
    (hp : edgeCondition a ↑A d p) (hr : d+r < q) (hK : K ≤ r) :
    (∑ j ∈ Finset.range (K+1), ∑ l ∈ Finset.range (min j (r-j)+1), q.choose l) ≤
      (K+1)*A.card := by
  classical
  let T : (Slot q r K → ℚ) →ₗ[ℚ] (↥A → Bounded (K+1)) :=
    { toFun := fun c x => ⟨pack a K c x.val, mem_degreeLT.mpr
        (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (pack_degree a K c x))))⟩
      map_add' := by
        intro c b; funext x; apply Subtype.ext
        change pack a K (c+b) x.val = pack a K c x.val + pack a K b x.val
        simp only [pack,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        simp [Nat.le_of_lt_succ u.val.1.isLt,add_mul]
      map_smul' := by
        intro z c; funext x; apply Subtype.ext
        change pack a K (z • c) x.val = z • pack a K c x.val
        simp only [pack, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro u _
        simp [Nat.le_of_lt_succ u.val.1.isLt, smul_eq_C_mul,mul_assoc] }
  have hT : Function.Injective T := by
    intro u v e
    apply sub_eq_zero.mp
    apply pack_restrict_injective ha hn hp hr _ _ hK
    intro x hx
    have : T (u-v) = 0 := by
      rw [sub_eq_add_neg,T.map_add,← neg_one_smul ℚ v,T.map_smul,e]; simp
    exact congrArg Subtype.val (congrFun this (⟨x,hx⟩ : ↥A))
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
