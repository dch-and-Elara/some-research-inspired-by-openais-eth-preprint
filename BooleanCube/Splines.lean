import BooleanCube.Budget
import Mathlib.RingTheory.Polynomial.DegreeLT

namespace LocalReconstruction
open Polynomial
open scoped Polynomial
noncomputable section

abbrev Bounded (n : ℕ) := Polynomial.degreeLT ℚ n

def sample {n : ℕ} (t : ℚ) : Bounded n →ₗ[ℚ] ℚ :=
  (Polynomial.leval t).comp (Bounded n).subtype

def splines {q : ℕ} (a : Fin q → ℚ) (k : ℕ) : Submodule ℚ (Cube q → Bounded (k+1)) where
  carrier := {f | ∀ i x, sample (a i) (f x) = sample (a i) (f (flip i x))}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg i x; simp [hf i x,hg i x]
  smul_mem' := by intro c f hf i x; simp [hf i x]

def rootSamples {q n : ℕ} (a : Fin q → ℚ) (s : Cube q) :
    Bounded n →ₗ[ℚ] (↥(ones s) → ℚ) := LinearMap.pi fun i => sample (a i)

theorem root_kernel_dim {q n : ℕ} {a : Fin q → ℚ} (ha : Function.Injective a) (s : Cube q) :
    Module.finrank ℚ (LinearMap.ker (rootSamples (n := n) a s)) = n - weight s := by
  classical
  let F := ones s
  let T := rootSamples (n := n) a s
  have hd : Module.finrank ℚ (Bounded n) = n := by
    simpa using (degreeLTEquiv ℚ n).finrank_eq
  by_cases hn : F.card ≤ n
  · have sur : Function.Surjective T := by
      intro y
      let v := fun i => if hi : i ∈ F then y ⟨i, hi⟩ else 0
      let u := Lagrange.interpolate F a v
      have hu : u ∈ Bounded F.card := mem_degreeLT.mpr (Lagrange.degree_interpolate_lt v ha.injOn)
      refine ⟨⟨u, degreeLT_mono hn hu⟩, ?_⟩
      funext i
      change u.eval (a i) = _
      exact (Lagrange.eval_interpolate_at_node v ha.injOn i.property).trans (dif_pos i.property)
    have hr := T.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr sur,finrank_top,Module.finrank_pi,Fintype.card_coe,hd] at hr
    change Module.finrank ℚ (LinearMap.ker T) = n - F.card
    change F.card + Module.finrank ℚ (LinearMap.ker T) = n at hr
    omega
  · have hz : LinearMap.ker T = ⊥ := by
      apply LinearMap.ker_eq_bot.mpr
      apply (injective_iff_map_eq_zero T).mpr
      intro f hf
      apply Subtype.ext
      by_contra ne
      have hdeg := mem_degreeLT.mp f.property
      change f.val ≠ 0 at ne
      rw [degree_eq_natDegree ne] at hdeg
      have hz := eq_zero_of_natDegree_lt_card_of_eval_eq_zero f.val (ha.comp (Subtype.val_injective (p := (· ∈ F))))
        (fun i => congrFun hf i) (by rw [Fintype.card_coe]; exact (WithBot.coe_lt_coe.mp hdeg).trans (Nat.lt_of_not_ge hn))
      exact ne hz
    change Module.finrank ℚ (LinearMap.ker T) = n - F.card
    rw [hz,finrank_bot]
    omega

private def transform {q : ℕ} {M : Type*} [AddCommGroup M] [Module ℚ M] :
    (Cube q → M) →ₗ[ℚ] (Cube q → M) where
  toFun f s := ∑ x : Cube q, walsh s x • f x
  map_add' f g := by ext1 s; simp [Finset.sum_add_distrib,smul_add]
  map_smul' c f := by ext1 s; simp [Finset.smul_sum,smul_comm (walsh _ _) c]

private theorem transform_twice {q : ℕ} {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : Cube q → M) (s : Cube q) : transform (transform f) s = (2^q : ℚ) • f s := by
  classical
  change (∑ x : Cube q, walsh s x • ∑ y : Cube q, walsh x y • f y) = _
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hu (y : Cube q) : (∑ x, walsh s x * walsh x y) = if s = y then (2:ℚ)^q else 0 := by
    simpa only [walsh_comm _ y] using walsh_orthogonal s y
  simp_rw [hu, ite_smul, zero_smul]
  simp

private theorem sample_transform {q n : ℕ} (f : Cube q → Bounded n) (s : Cube q) (t : ℚ) :
    sample t (transform f s) = ∑ x, walsh s x * sample t (f x) := by
  simp [transform, map_sum]

private theorem forward_roots {q k : ℕ} {a : Fin q → ℚ} (f : splines a k) (s : Cube q) :
    transform f.val s ∈ LinearMap.ker (rootSamples a s) := by
  apply LinearMap.mem_ker.mpr
  funext i
  change sample (a i) (transform f.val s) = 0
  rw [sample_transform]
  have e := (flipEquiv i.val).sum_comp (fun x => walsh s x * sample (a i) (f.val x))
  change (∑ x, walsh s (flip i x) * sample (a i) (f.val (flip i x))) = _ at e
  have hs : s i = true := (Finset.mem_filter.mp i.property).2
  have h (x : Cube q) : walsh s (flip i x) = -walsh s x := by
    rw [walsh_comm s _,walsh_flip,walsh_comm x s,hs]; simp [signBit]
  simp_rw [h, ← f.property i _,neg_mul,Finset.sum_neg_distrib] at e
  linarith

private theorem back_edges {q k : ℕ} {a : Fin q → ℚ}
    (g : (s : Cube q) → LinearMap.ker (rootSamples (n := k+1) a s)) :
    transform (fun s => (g s).val) ∈ splines a k := by
  intro i x
  rw [sample_transform,sample_transform]
  apply Finset.sum_congr rfl
  intro s _
  rw [walsh_flip]
  cases hs : s i with
  | false => simp [signBit]
  | true =>
    have hi : i ∈ ones s := by simp [ones,hs]
    have hz := congrFun (LinearMap.mem_ker.mp (g s).property) (⟨i,hi⟩ : ↥(ones s))
    change sample (a i) (g s).val = 0 at hz
    simp [hz]

def splineSpectrum {q k : ℕ} (a : Fin q → ℚ) : splines a k ≃ₗ[ℚ]
    ((s : Cube q) → LinearMap.ker (rootSamples (n := k+1) a s)) where
  toFun f s := ⟨transform f.val s, forward_roots f s⟩
  invFun g := ⟨((2:ℚ)^q)⁻¹ • transform (fun s => (g s).val),
    (splines a k).smul_mem _ (back_edges g)⟩
  left_inv f := by
    apply Subtype.ext
    funext s
    change ((2:ℚ)^q)⁻¹ • transform (transform f.val) s = f.val s
    simp [transform_twice,smul_smul]
  right_inv g := by
    funext s
    apply Subtype.ext
    change transform (((2:ℚ)^q)⁻¹ • transform (fun s => (g s).val)) s = _
    rw [map_smul, Pi.smul_apply,transform_twice,smul_smul]
    simp
  map_add' f g := by funext s; apply Subtype.ext; exact congrFun (transform.map_add f.val g.val) s
  map_smul' c f := by funext s; apply Subtype.ext; exact congrFun (transform.map_smul c f.val) s

theorem spline_dimension {q k : ℕ} {a : Fin q → ℚ} (ha : Function.Injective a) :
    Module.finrank ℚ (splines a k) = ∑ j ∈ Finset.range (q+1), (k+1-j) * q.choose j := by
  classical
  rw [(splineSpectrum (k := k) a).finrank_eq]
  letI (s : Cube q) : Module.Free ℚ (LinearMap.ker (rootSamples (n := k+1) a s)) := by
    apply @Module.Free.of_divisionRing ℚ ↥(LinearMap.ker (rootSamples (n := k+1) a s)) _ _ _
  letI (s : Cube q) : Module.Finite ℚ (LinearMap.ker (rootSamples (n := k+1) a s)) :=
    inferInstance
  rw [Module.finrank_pi_fintype ℚ]
  simp_rw [root_kernel_dim ha]
  have hw (s : Cube q) (_ : s ∈ Finset.univ) : weight s ∈ Finset.range (q+1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (by simpa [weight] using (ones s).card_le_univ)
  rw [← Finset.sum_fiberwise_of_maps_to hw]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ _s ∈ (Finset.univ.filter fun s : Cube q => weight s = j), (k+1-j) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ = _ := by simp [layer_size,Nat.mul_comm]

end
end LocalReconstruction
