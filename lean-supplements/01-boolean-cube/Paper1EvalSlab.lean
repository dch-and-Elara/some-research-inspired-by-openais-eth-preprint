import Paper1EvalKernel

/-! Paper 1, §6.1: exact ambient Walsh evaluation image and the
bilinear dimension filtration of the actual restricted spline space. -/

namespace LocalReconstruction.Paper1Coverage

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

def evaluateSpline {q : ℕ} (a : Fin q → ℚ) (k : ℕ) :
    splines a k →ₗ[ℚ] (Cube q → ℚ) :=
  LinearMap.pi fun x => (sample (0:ℚ)).comp
    ((LinearMap.proj (R := ℚ) x).comp (splines a k).subtype)

private theorem eval_bounded_degree {k : ℕ} (p : Bounded (k+1)) : p.val.natDegree ≤ k := by
  by_cases hz : p.val = 0
  · simp [hz]
  have hd := mem_degreeLT.mp p.property
  rw [degree_eq_natDegree hz] at hd
  exact Nat.le_of_lt_succ (WithBot.coe_lt_coe.mp hd)

/-- A frequency of weight higher than the degree cutoff has zero coefficient
in the full (not just restricted) evaluation image. -/
theorem higher_frequency_evaluation_vanishes {q j : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (h : splines a j) (s : Cube q) (hs : j < weight s) :
    coefficient s (evaluateSpline a j h) = 0 := by
  let f := splineSpectrum (k := j) a h s
  have roots (i : ↥(ones s)) : f.val.val.eval (a i.val) = 0 := by
    exact congrFun (LinearMap.mem_ker.mp f.property) i
  have zeroPoly : f.val.val = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero f.val.val
      (ha.comp Subtype.val_injective) roots
    rw [Fintype.card_coe]
    exact (eval_bounded_degree f.val).trans_lt hs
  have ev : sample 0 f.val = 0 := by
    change f.val.val.eval 0 = 0
    simp [zeroPoly]
  change sample 0 (∑ x : Cube q, walsh s x • h.val x) = 0 at ev
  simp only [map_sum, map_smul, smul_eq_mul] at ev
  calc
    coefficient s (evaluateSpline a j h) = ∑ x : Cube q, walsh s x * sample 0 (h.val x) := by
      unfold coefficient
      apply Finset.sum_congr rfl
      intro x _
      change sample 0 (h.val x) * walsh s x = walsh s x * sample 0 (h.val x)
      exact mul_comm _ _
    _ = 0 := ev

private theorem walsh_member_from_coeff {q : ℕ} {B : Set (Cube q)} (f : Cube q → ℚ)
    (hf : ∀ s ∉ B, coefficient s f = 0) : f ∈ walshSpace B := by
  have sumMem : (∑ s : Cube q, coefficient s f • walsh s) ∈ walshSpace B := by
    apply Submodule.sum_mem
    intro s _
    by_cases hs : s ∈ B
    · exact (walshSpace B).smul_mem _ (Submodule.subset_span ⟨s, hs, rfl⟩)
    · simpa only [hf s hs, zero_smul] using (walshSpace B).zero_mem
  have formula : (∑ s : Cube q, coefficient s f • walsh s) = (2^q : ℚ) • f := by
    funext x
    simpa [coefficient, Finset.sum_apply] using synthesis f x
  rw [formula] at sumMem
  have h := (walshSpace B).smul_mem ((2:ℚ)^q)⁻¹ sumMem
  simpa [smul_smul] using h

/-- Exact test-family formula from the paper: one Walsh mode times the
normalized product of its direction factors `1-X/a_i`. -/
def evaluationMode {q : ℕ} (a : Fin q → ℚ) (s x : Cube q) : ℚ[X] :=
  C (walsh x s) * ∏ i ∈ ones s, (1 - C (a i)⁻¹ * X)

theorem evaluationMode_zero {q : ℕ} (a : Fin q → ℚ) (s x : Cube q) :
    (evaluationMode a s x).eval 0 = walsh s x := by
  simp [evaluationMode, eval_prod, walsh_comm x s]

theorem evaluationMode_degree {q : ℕ} (a : Fin q → ℚ) (s x : Cube q) :
    (evaluationMode a s x).natDegree ≤ weight s := by
  apply (natDegree_C_mul_le ..).trans
  apply (natDegree_prod_le ..).trans
  calc
    _ ≤ ∑ _i ∈ ones s, 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (natDegree_sub_le ..).trans
      exact max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp))
    _ = weight s := by simp [weight]

theorem evaluationMode_edges {q : ℕ} {a : Fin q → ℚ} (hn : ∀ i, a i ≠ 0)
    (s : Cube q) : EqualEdges a (evaluationMode a s) := by
  intro i x
  simp only [evaluationMode, eval_mul, eval_C, eval_prod, walsh_flip]
  cases hs : s i with
  | false => simp [signBit]
  | true =>
    have hi : i ∈ ones s := by simp [ones, hs]
    have z : (∏ t ∈ ones s, eval (a i) (1 - C (a t)⁻¹ * X)) = 0 :=
      Finset.prod_eq_zero hi (by simp [hn i])
    simp only [z, mul_zero]

/-- The exact image of all `H_l` under evaluation, not an assumed image. -/
theorem ambient_evaluation_image {q j : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) :
    LinearMap.range (evaluateSpline a j) = walshSpace {s | weight s ≤ j} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨h, rfl⟩ := LinearMap.mem_range.mp hg
    apply walsh_member_from_coeff
    intro s hs
    refine higher_frequency_evaluation_vanishes ha h s ?_
    exact Nat.lt_of_not_ge hs
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, hs, rfl⟩
    apply LinearMap.mem_range.mpr
    let g : Cube q → Bounded (j+1) := fun x =>
      ⟨evaluationMode a s x, mem_degreeLT.mpr (lt_of_le_of_lt degree_le_natDegree
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le ((evaluationMode_degree a s x).trans hs))))⟩
    refine ⟨⟨g, evaluationMode_edges hn s⟩, ?_⟩
    funext x
    exact evaluationMode_zero a s x

theorem lower_frequency_vanishing_evaluation {q d j r : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) {A : Finset (Cube q)}
    {p : Cube q → ℚ[X]} (hp : edgeCondition a ↑A d p) (hr : d+r < q) (hj : j ≤ r)
    (h : vanishingSplines a j A) (s : Cube q) (hs : weight s ≤ r-j) :
    coefficient s (evalVanishing a j A h) = 0 := by
  have cert := bilinear_certificate ha hp (vanishingPolynomial_edges h) (evaluationMode_edges hn s)
    (vanishingPolynomial_deleted h) (vanishingPolynomial_degree h)
    (fun x => (evaluationMode_degree a s x).trans hs) (by omega : d+j+(r-j) < q)
  simpa only [evaluationMode_zero, coefficient, evalVanishing_apply] using cert

/-- The paper's inclusion `V_j` in the precise Walsh frequency slab. -/
theorem vanishing_evaluation_image_in_slab {q d j r : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) {A : Finset (Cube q)}
    {p : Cube q → ℚ[X]} (hp : edgeCondition a ↑A d p) (hr : d+r < q) (hj : j ≤ r) :
    vanishingImage a j A ≤ walshSpace {s | r-j < weight s ∧ weight s ≤ j} := by
  intro g hg
  obtain ⟨h, rfl⟩ := LinearMap.mem_range.mp hg
  apply walsh_member_from_coeff
  intro s hs
  by_cases hw : weight s ≤ j
  · exact lower_frequency_vanishing_evaluation ha hn hp hr hj h s
      (Nat.le_of_not_gt fun H => hs ⟨H, hw⟩)
  · change coefficient s (evaluateSpline a j h.val) = 0
    exact higher_frequency_evaluation_vanishes ha h.val s (Nat.lt_of_not_ge hw)

def binomialPrefix (q j : ℕ) : ℕ :=
  ∑ l ∈ Finset.range (j+1), q.choose l

/-- The rank of the exact Walsh slab is `B_j-B_min(j,r-j)`. -/
theorem slab_finrank (q j r : ℕ) :
    Module.finrank ℚ (walshSpace {s : Cube q | r-j < weight s ∧ weight s ≤ j}) =
      binomialPrefix q j - binomialPrefix q (min j (r-j)) := by
  classical
  let K := (Finset.range (j+1)).filter (fun w => r-j < w)
  have he : ({s : Cube q | r-j < weight s ∧ weight s ≤ j} : Set (Cube q)) =
      layerFamily q K := by
    ext s
    simp only [Set.mem_setOf_eq, layerFamily, K, Finset.mem_filter, Finset.mem_range]
    omega
  rw [he, layer_rank]
  have hfilter : (Finset.range (j+1)).filter (fun w => ¬(r-j < w)) =
      Finset.range (min j (r-j)+1) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range (j+1))
    (p := fun w => r-j < w) (f := q.choose)
  rw [hfilter] at hsplit
  change (∑ w ∈ K, q.choose w) + binomialPrefix q (min j (r-j)) = binomialPrefix q j at hsplit
  omega

theorem vanishing_evaluation_dimension_bound {q d j r : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) {A : Finset (Cube q)}
    {p : Cube q → ℚ[X]} (hp : edgeCondition a ↑A d p) (hr : d+r < q) (hj : j ≤ r) :
    Module.finrank ℚ (vanishingImage a j A) ≤
      binomialPrefix q j - binomialPrefix q (min j (r-j)) := by
  rw [← slab_finrank]
  exact Submodule.finrank_mono (vanishing_evaluation_image_in_slab ha hn hp hr hj)

theorem vanishing_dimension_bound {q d K r : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) {A : Finset (Cube q)}
    {p : Cube q → ℚ[X]} (hp : edgeCondition a ↑A d p) (hr : d+r < q) (hK : K ≤ r) :
    Module.finrank ℚ (vanishingSplines a K A) ≤
      ∑ j ∈ Finset.range (K+1), (binomialPrefix q j - binomialPrefix q (min j (r-j))) := by
  rw [vanishing_dimension_sum hn]
  apply Finset.sum_le_sum
  intro j hj
  exact vanishing_evaluation_dimension_bound ha hn hp hr
    ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hK)

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.higher_frequency_evaluation_vanishes
#print axioms LocalReconstruction.Paper1Coverage.evaluationMode_zero
#print axioms LocalReconstruction.Paper1Coverage.evaluationMode_degree
#print axioms LocalReconstruction.Paper1Coverage.evaluationMode_edges
#print axioms LocalReconstruction.Paper1Coverage.ambient_evaluation_image
#print axioms LocalReconstruction.Paper1Coverage.lower_frequency_vanishing_evaluation
#print axioms LocalReconstruction.Paper1Coverage.vanishing_evaluation_image_in_slab
#print axioms LocalReconstruction.Paper1Coverage.slab_finrank
#print axioms LocalReconstruction.Paper1Coverage.vanishing_evaluation_dimension_bound
#print axioms LocalReconstruction.Paper1Coverage.vanishing_dimension_bound
