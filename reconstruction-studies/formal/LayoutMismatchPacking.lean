import LayoutMismatchTensor

namespace Reconstruction.LayoutMismatch
open Polynomial Matrix
open LayoutBudget (GroupFiber)
open scoped Polynomial
noncomputable section

variable {I V G : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G]

def groupSlope (g : G) : ℚ := (Fintype.equivFin G g).val

omit [DecidableEq G] in
theorem groupSlope_injective : Function.Injective (groupSlope (G := G)) := by
  intro g h eq
  apply (Fintype.equivFin G).injective
  apply Fin.ext
  change ((Fintype.equivFin G g).val : ℚ) = (Fintype.equivFin G h).val at eq
  exact_mod_cast eq

def layoutWord (a b : I → V → G) (v : V) : Word I :=
  fun t => (groupSlope (a t v), groupSlope (b t v))

private theorem row_annihilated {V G : Type*} [Fintype V] [Fintype G] [DecidableEq G]
    {M : G → Type*} [∀ g, Fintype (M g)]
    (a : V → G) (b : G) (r p : V → ℚ) (C : ∀ g, Matrix (M g) (GroupFiber a g) ℚ)
    (foreign : ∀ g, b ≠ g → (fun v : GroupFiber a g => r v.val) ∈
      Submodule.span ℚ (Set.range (C g).row))
    (kernel : ∀ g i, ∑ v, C g i v * p v.val = 0)
    (allowed : ∀ v, a v = b → p v = 0) :
    ∑ v, r v * p v = 0 := by
  rw [← (Equiv.sigmaFiberEquiv a).sum_comp (fun v => r v * p v), Fintype.sum_sigma]
  apply Finset.sum_eq_zero
  intro g _
  change (∑ v : GroupFiber a g, r v.val * p v.val) = 0
  by_cases hg : b = g
  · apply Finset.sum_eq_zero
    intro v _
    rw [allowed v.val (v.property.trans hg.symm), mul_zero]
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (foreign g hg)
    have hc' (v : GroupFiber a g) : (∑ i, c i * C g i v) = r v.val := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply] using
        congrFun hc v
    simp_rw [← hc', Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, kernel g, mul_zero]
    exact Finset.sum_const_zero

section
variable {M : I → G → Type*} [∀ t g, Fintype (M t g)]

/-- A one-row contraction for different measurement matrices at each node. -/
theorem matrix_tensor_certificate (nodes : I → ℚ) (a b : I → V → G)
    (C : ∀ t g, Matrix (M t g) (GroupFiber (a t) g) ℚ)
    (P : Matrix V V ℚ[X]) (hq : Function.Injective nodes) (R j l : ℕ)
    (hzero : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hdegree : ∀ u v, (P u v).natDegree ≤ R)
    (w : V)
    (hforeign : ∀ t g, b t w ≠ g →
      (fun v : GroupFiber (a t) g => (P w v.val).eval (nodes t)) ∈
        Submodule.span ℚ (Set.range (C t g).row))
    (h : V → Mask I → ℚ[X]) (test : Mask I → ℚ[X])
    (hpair : ∀ t v, a t v = b t w →
      ∑ x, (test x).eval (nodes t) * (h v x).eval (nodes t) = 0)
    (hk : ∀ t g i x, ∑ v : GroupFiber (a t) g, C t g i v * (h v.val x).eval (nodes t) = 0)
    (hj : ∀ v x, (h v x).natDegree ≤ j) (hl : ∀ x, (test x).natDegree ≤ l)
    (hd : R + j + l < Fintype.card I) :
    ∑ x, (test x).eval 0 * (h w x).eval 0 = 0 := by
  let p (v : V) : ℚ[X] := ∑ x, test x * h v x
  let F : ℚ[X] := ∑ v, P w v * p v
  have hpdeg (v : V) : (p v).natDegree ≤ j + l := by
    apply natDegree_sum_le_of_forall_le
    intro x _
    exact natDegree_mul_le.trans (by simpa [Nat.add_comm] using Nat.add_le_add (hl x) (hj v x))
  have hdeg : F.natDegree ≤ R + j + l := by
    apply natDegree_sum_le_of_forall_le
    intro v _
    exact natDegree_mul_le.trans
      (by simpa [Nat.add_assoc] using Nat.add_le_add (hdegree w v) (hpdeg v))
  have roots (t : I) : F.eval (nodes t) = 0 := by
    simp only [F, eval_finset_sum, eval_mul]
    apply row_annihilated (a t) (b t w) (fun v => (P w v).eval (nodes t))
      (fun v => (p v).eval (nodes t)) (C t) (hforeign t)
    · intro g i
      simp only [p, eval_finset_sum, eval_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [mul_left_comm _ ((test _).eval (nodes t)), ← Finset.mul_sum, hk t g i, mul_zero]
      exact Finset.sum_const_zero
    · intro v hv
      simpa only [p, eval_finset_sum, eval_mul] using hpair t v hv
  have hF := eq_zero_of_natDegree_lt_card_of_eval_eq_zero F hq roots (hdeg.trans_lt hd)
  have hz := congrArg (eval (0 : ℚ)) hF
  simpa [F, p, eval_finset_sum, hzero, ite_mul] using hz

end

/-- A slot for each retained physical input mode at each eligible degree level. -/
abbrev Slot (w : V → Word I) (J : ℕ) :=
  {u : Fin (J + 1) × V × Mask I //
    weight u.2.2 ≤ u.1.val ∧ weight (dualMask (w u.2.1) u.2.2) ≤ J - u.1.val}

variable (w : V → Word I) {J : ℕ}

private def packCoeff (L : ℕ) (c : Slot w J → ℚ) (v : V) (u : Slot w J) : ℚ[X] :=
  if u.val.1.val ≤ L ∧ v = u.val.2.1 then C (c u) * X ^ (L - u.val.1.val) else 0

private def pack (nodes : I → ℚ) (L : ℕ) (c : Slot w J → ℚ) (v : V) (x : Mask I) : ℚ[X] :=
  ∑ u, packCoeff w L c v u * inputMode nodes (w v) u.val.2.2 x

private theorem pack_degree (nodes : I → ℚ) (L : ℕ) (c : Slot w J → ℚ) (v : V) (x : Mask I) :
    (pack w nodes L c v x).natDegree ≤ L := by
  apply natDegree_sum_le_of_forall_le
  intro u _
  by_cases hu : u.val.1.val ≤ L ∧ v = u.val.2.1
  · rw [packCoeff, if_pos hu, mul_assoc]
    apply (natDegree_C_mul_le ..).trans
    apply natDegree_mul_le.trans
    rw [natDegree_X_pow]
    have hd := (inputMode_degree nodes (w v) u.val.2.2 x).trans u.property.1
    have := hu.1
    omega
  · rw [packCoeff, if_neg hu, zero_mul, natDegree_zero]
    exact Nat.zero_le _

private def packLinear (nodes : I → ℚ) :
    (Slot w J → ℚ) →ₗ[ℚ] (V → Mask I → ℚ[X]) where
  toFun := pack w nodes J
  map_add' c b := by
    funext v x
    simp only [pack, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    unfold packCoeff
    split_ifs <;> simp [add_mul]
  map_smul' z c := by
    funext v x
    simp only [pack, Pi.smul_apply, RingHom.id_apply, smul_eq_C_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    unfold packCoeff
    split_ifs <;> simp [mul_assoc]

private theorem pack_pair_at_zero (nodes : I → ℚ) (c : Slot w J → ℚ) (u : Slot w J) :
    ∑ x, (outputTest nodes (w u.val.2.1) (dualMask (w u.val.2.1) u.val.2.2) x).eval 0 *
      (pack w nodes u.val.1.val c u.val.2.1 x).eval 0 = c u := by
  simp only [pack, eval_finset_sum, eval_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm _ (eval 0 (packCoeff _ _ _ _ _)), ← Finset.mul_sum,
    outputTest_dot_inputMode_zero]
  rw [Finset.sum_eq_single u]
  · simp [packCoeff]
  · intro v _ hne
    by_cases hj : v.val.1.val = u.val.1.val
    · by_cases hw : u.val.2.1 = v.val.2.1
      · have hs : dualMask (w u.val.2.1) u.val.2.2 ≠ dualMask (w u.val.2.1) v.val.2.2 := by
          intro hb
          have hmask := dualMask_injective (w u.val.2.1) hb
          exact hne (Subtype.ext (Prod.ext (Fin.ext hj) (Prod.ext hw.symm hmask.symm)))
        simp [hs]
      · simp [packCoeff, hw]
    · by_cases hle : v.val.1.val ≤ u.val.1.val ∧ u.val.2.1 = v.val.2.1
      · have hdiff : u.val.1.val - v.val.1.val ≠ 0 := by have := hle.1; omega
        simp [packCoeff, hle, hdiff]
      · rw [packCoeff, if_neg hle, eval_zero, zero_mul]
  · simp

private theorem pack_pair_at_node (nodes : I → ℚ) (L : ℕ) (c : Slot w J → ℚ)
    (u v : V) (B : Mask I) (t : I) (hn : nodes t ≠ 0) (hv : (w v t).1 = (w u t).2) :
    ∑ x, (outputTest nodes (w u) B x).eval (nodes t) *
      (pack w nodes L c v x).eval (nodes t) = 0 := by
  simp only [pack, eval_finset_sum, eval_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  simp_rw [mul_left_comm _ ((packCoeff w L c v i).eval (nodes t)), ← Finset.mul_sum]
  rw [outputTest_half_pair nodes (w u) (w v) B i.val.2.2 t hn hv, mul_zero]

private theorem pack_eval_split (nodes : I → ℚ) (L : ℕ) (c : Slot w J → ℚ)
    (v : V) (t : I) (x : Mask I) (hn : nodes t ≠ 0) :
    (pack w nodes L c v x).eval (nodes t) =
      lowFactor (w v t).1 (x t) *
        (pack w nodes L c v (extendZero t (fun i => x i.val))).eval (nodes t) := by
  simp only [pack, eval_finset_sum, eval_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_inputMode_split nodes (w v) i.val.2.2 x t hn]
  exact mul_left_comm _ _ _

section
variable {M : I → G → Type*} [∀ t g, Fintype (M t g)]
variable (nodes : I → ℚ) (a b : I → V → G)
variable (C : ∀ t g, Matrix (M t g) (GroupFiber (a t) g) ℚ)
local notation "ww" => layoutWord a b

private theorem pack_kernel_trivial
    (hq : Function.Injective nodes) (hn : ∀ t, nodes t ≠ 0)
    (P : Matrix V V ℚ[X]) (R J : ℕ) (hJ : J + R < Fintype.card I)
    (hzero : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hdegree : ∀ u v, (P u v).natDegree ≤ R)
    (hforeign : ∀ t u g, b t u ≠ g →
      (fun v : GroupFiber (a t) g => (P u v.val).eval (nodes t)) ∈
        Submodule.span ℚ (Set.range (C t g).row))
    (c : Slot ww J → ℚ)
    (hker : ∀ t g i (x : Half t),
      ∑ v : GroupFiber (a t) g, C t g i v *
        (pack ww nodes J c v.val (extendZero t x)).eval (nodes t) = 0) :
    c = 0 := by
  classical
  by_contra hc
  let support := Finset.univ.filter (fun u => c u ≠ 0)
  have hs : support.Nonempty := by
    by_contra! h
    apply hc
    funext u
    by_contra ne
    have hu : u ∈ support := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne⟩
    exact h ⟨u, hu⟩
  obtain ⟨u, hu, hmax⟩ := support.exists_max_image (fun v => v.val.1.val) hs
  let L := u.val.1.val
  have hLJ : L ≤ J := Nat.le_of_lt_succ u.val.1.isLt
  have cut (v : Slot ww J) (h : ¬v.val.1.val ≤ L) : c v = 0 := by
    by_contra ne
    exact h (hmax v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne⟩))
  have factor (v : V) (x : Mask I) :
      X ^ (J - L) * pack ww nodes L c v x = pack ww nodes J c v x := by
    simp only [pack, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    have hz : z.val.1.val ≤ J := Nat.le_of_lt_succ z.val.1.isLt
    by_cases hv : v = z.val.2.1
    · by_cases h : z.val.1.val ≤ L
      · simp only [packCoeff, hz, hv, and_self, if_true, h]
        rw [show J - z.val.1.val = J - L + (L - z.val.1.val) by omega, pow_add]
        ring
      · simp [packCoeff, h, hv, cut z h]
    · simp [packCoeff, hv]
  have halfZero (t : I) (g : G) (i : M t g) (x : Half t) :
      ∑ v : GroupFiber (a t) g, C t g i v *
        (pack ww nodes L c v.val (extendZero t x)).eval (nodes t) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero (J - L) (hn t))
    rw [Finset.mul_sum, ← hker t g i x]
    apply Finset.sum_congr rfl
    intro v _
    rw [← factor v.val (extendZero t x), eval_mul, eval_X_pow]
    exact mul_left_comm _ _ _
  have fullZero (t : I) (g : G) (i : M t g) (x : Mask I) :
      ∑ v : GroupFiber (a t) g, C t g i v * (pack ww nodes L c v.val x).eval (nodes t) = 0 := by
    calc
      _ = lowFactor (groupSlope g) (x t) *
          ∑ v : GroupFiber (a t) g, C t g i v *
            (pack ww nodes L c v.val (extendZero t (fun j => x j.val))).eval (nodes t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        rw [pack_eval_split ww nodes L c v.val t x (hn t)]
        rw [show (ww v.val t).1 = groupSlope g from congrArg groupSlope v.property]
        exact mul_left_comm _ _ _
      _ = 0 := by rw [halfZero, mul_zero]
  let B := dualMask (ww u.val.2.1) u.val.2.2
  have bound : R + L + weight B < Fintype.card I := by
    have hout := u.property.2
    dsimp [B, L] at *
    omega
  have orth := matrix_tensor_certificate nodes a b C P hq R L (weight B) hzero hdegree
    u.val.2.1 (fun t g => hforeign t u.val.2.1 g)
    (pack ww nodes L c) (outputTest nodes (ww u.val.2.1) B)
    (fun t v hv => pack_pair_at_node ww nodes L c u.val.2.1 v B t (hn t) (congrArg groupSlope hv))
    fullZero (pack_degree ww nodes L c) (outputTest_degree nodes (ww u.val.2.1) B) bound
  exact (Finset.mem_filter.mp hu).2 ((pack_pair_at_zero ww nodes c u).symm.trans orth)

/-- Nodal measurement with the full matrix range at each half-mask coordinate. -/
private def evalHalf (t : I) (g : G) (x : Half t) :
    (V → Mask I → ℚ[X]) →ₗ[ℚ] (GroupFiber (a t) g → ℚ) where
  toFun := fun h v => (h v.val (extendZero t x)).eval (nodes t)
  map_add' := by intro f h; funext v; simp
  map_smul' := by intro z f; funext v; simp [smul_eq_C_mul, eval_mul]

theorem slot_card_le_node_ranks
    (hq : Function.Injective nodes) (hn : ∀ t, nodes t ≠ 0)
    (P : Matrix V V ℚ[X]) (R J : ℕ) (hJ : J + R < Fintype.card I)
    (hzero : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hdegree : ∀ u v, (P u v).natDegree ≤ R)
    (hforeign : ∀ t u g, b t u ≠ g →
      (fun v : GroupFiber (a t) g => (P u v.val).eval (nodes t)) ∈
        Submodule.span ℚ (Set.range (C t g).row)) :
    Fintype.card (Slot ww J) ≤
      2 ^ (Fintype.card I - 1) * ∑ t, ∑ g, (C t g).rank := by
  let T : (Slot ww J → ℚ) →ₗ[ℚ]
      (∀ t : I, ∀ g : G, Half t → LinearMap.range (C t g).mulVecLin) :=
    LinearMap.pi fun t => LinearMap.pi fun g => LinearMap.pi fun x =>
      (C t g).mulVecLin.rangeRestrict.comp ((evalHalf nodes a t g x).comp (packLinear ww nodes))
  have hT : Function.Injective T := LinearMap.ker_eq_bot.mp (by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    apply pack_kernel_trivial nodes a b C hq hn P R J hJ hzero hdegree hforeign c
    intro t g i x
    have eq := congrArg (fun z : LinearMap.range (C t g).mulVecLin => z.val i)
      (congrFun (congrFun (congrFun hc t) g) x)
    simpa [T, packLinear, evalHalf, Matrix.mulVec, dotProduct] using eq)
  have dim := LinearMap.finrank_le_finrank_of_injective hT
  rw [Module.finrank_pi] at dim
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_half, ← Finset.mul_sum] at dim
  simpa only [Matrix.rank] using dim

end
end
end Reconstruction.LayoutMismatch
