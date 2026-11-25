import DeterminantBudget

/-!
# Principal-subset imbalance for node-dependent reconstruction

Theorem 1 of the first v2 paper, *Rank lower bounds for node-dependent
polynomial reconstruction in SAT counting*. The model uses source labels on
physical variables, target labels on selected incidence rows, and separate
measurement matrices for each node and source group.
-/

open scoped BigOperators
open Polynomial Matrix

namespace Reconstruction
namespace LayoutBudget

noncomputable section

/-- The physical variables in one source group, or rows assigned to one target group. -/
abbrev GroupFiber {V G : Type*} (a : V → G) (g : G) := {v : V // a v = g}

/-- Retain all measurement rows and only the selected columns in group `g`. -/
def restrictGroupMatrix {F V U G M : Type*} (ι : U → V) (a : V → G) (g : G)
    (C : Matrix M (GroupFiber a g) F) : Matrix M (GroupFiber (a ∘ ι) g) F :=
  C.submatrix id (fun v => ⟨ι v.val, v.property⟩)

/-- The sum of actual ranks of the group measurement matrices on the selected columns. -/
def measurementRank {F V U G : Type*} [Field F] [Fintype U] [Fintype G] [DecidableEq G]
    {M : G → Type*} (ι : U → V) (a : V → G)
    (C : ∀ g, Matrix (M g) (GroupFiber a g) F) : ℕ :=
  ∑ g, (restrictGroupMatrix ι a g (C g)).rank

/-- The sum of absolute source/target count differences, before dividing by two. -/
def twiceImbalance {U G : Type*} [Fintype U] [Fintype G] [DecidableEq G]
    (a b : U → G) : ℕ :=
  ∑ g, Int.natAbs
    ((Fintype.card (GroupFiber a g) : ℤ) - Fintype.card (GroupFiber b g))

variable {F : Type*} [Field F]

private theorem rank_add_bound {U V : Type*} [Fintype U] [Fintype V]
    (A B : Matrix U V F) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

private theorem rank_sum_bound {U V G : Type*} [Fintype U] [Fintype V]
    (s : Finset G) (A : G → Matrix U V F) :
    (∑ g ∈ s, A g).rank ≤ ∑ g ∈ s, (A g).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert g s hg ih =>
    simpa only [Finset.sum_insert hg] using
      (rank_add_bound (A g) (∑ i ∈ s, A i)).trans (Nat.add_le_add_left ih _)

private def groupInclusion {U G : Type*} [DecidableEq U] (a : U → G) (g : G) :
    Matrix (GroupFiber a g) U F :=
  Matrix.of (fun v u => if v.val = u then 1 else 0)

private theorem mul_groupInclusion {W U G : Type*} [Fintype U] [DecidableEq U]
    [DecidableEq G] (a : U → G) (g : G) (A : Matrix W (GroupFiber a g) F)
    (w : W) (u : U) :
    (A * groupInclusion (F := F) a g) w u = if h : a u = g then A w ⟨u, h⟩ else 0 := by
  simp only [Matrix.mul_apply, groupInclusion, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · have hval (v : GroupFiber a g) : v.val = u ↔ v = (⟨u, h⟩ : GroupFiber a g) :=
      by
      constructor
      · intro e
        apply Subtype.ext
        exact e
      · intro e
        exact congrArg Subtype.val e
    simp [hval]
  · apply Finset.sum_eq_zero
    intro v _
    have hne : v.val ≠ u := by
      intro e
      exact h (by simpa only [← e] using v.property)
    rw [if_neg hne]

private theorem groupInclusion_transpose_mul {W U G : Type*} [Fintype U] [DecidableEq U]
    [DecidableEq G] (a : U → G) (g : G) (A : Matrix (GroupFiber a g) W F)
    (u : U) (w : W) :
    ((groupInclusion (F := F) a g)ᵀ * A) u w = if h : a u = g then A ⟨u, h⟩ w else 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, groupInclusion, Matrix.of_apply,
    ite_mul, one_mul, zero_mul]
  split_ifs with h
  · have hval (v : GroupFiber a g) : v.val = u ↔ v = (⟨u, h⟩ : GroupFiber a g) :=
      by
      constructor
      · intro e
        apply Subtype.ext
        exact e
      · intro e
        exact congrArg Subtype.val e
    simp [hval]
  · apply Finset.sum_eq_zero
    intro v _
    have hne : v.val ≠ u := by
      intro e
      exact h (by simpa only [← e] using v.property)
    rw [if_neg hne]

/-- One-node block rank bound for equation (1), already restricted on the
output side. The selected input columns are given by `ι`. -/
theorem restricted_rank_le {V U G : Type*} [Fintype U] [Fintype G] [DecidableEq G]
    {M : G → Type*} [∀ g, Fintype (M g)]
    (ι : U → V) (a : V → G) (b : U → G) (A : Matrix U V F)
    (C : ∀ g, Matrix (M g) (GroupFiber a g) F)
    (hforeign : ∀ u g, b u ≠ g →
      (fun v : GroupFiber a g => A u v.val) ∈ Submodule.span F (Set.range (C g).row)) :
    (A.submatrix id ι).rank ≤ measurementRank ι a C +
      ∑ g, min (Fintype.card (GroupFiber (a ∘ ι) g)) (Fintype.card (GroupFiber b g)) := by
  classical
  have hcoeff (u : U) (g : G) (h : b u ≠ g) :
      ∃ c : M g → F, ∀ v : GroupFiber a g, ∑ i, c i * C g i v = A u v.val := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp (hforeign u g h)
    refine ⟨c, fun v => ?_⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply] using
      congrFun hc v
  let D (g : G) : Matrix U (M g) F :=
    Matrix.of (fun u i => if h : b u ≠ g then Classical.choose (hcoeff u g h) i else 0)
  let B (g : G) : Matrix (GroupFiber b g) (GroupFiber (a ∘ ι) g) F :=
    Matrix.of (fun u v => A u.val (ι v.val))
  let L (g : G) : Matrix U U F :=
    (groupInclusion b g)ᵀ * B g * groupInclusion (a ∘ ι) g
  let N (g : G) : Matrix U U F :=
    D g * restrictGroupMatrix ι a g (C g) * groupInclusion (a ∘ ι) g
  have hdecomp : A.submatrix id ι = ∑ g, (L g + N g) := by
    ext u v
    simp only [Matrix.submatrix_apply, id_eq, Matrix.sum_apply, Matrix.add_apply]
    let g := a (ι v)
    rw [Finset.sum_eq_single g]
    · have hv : (a ∘ ι) v = g := rfl
      simp only [L, N, mul_groupInclusion, dif_pos hv, groupInclusion_transpose_mul]
      by_cases hu : b u = g
      · simp [hu, B, D, Matrix.mul_apply]
      · rw [dif_neg hu, zero_add, Matrix.mul_apply]
        simpa only [D, Matrix.of_apply, dif_pos hu, restrictGroupMatrix, Matrix.submatrix_apply,
          id_eq] using (Classical.choose_spec (hcoeff u g hu) ⟨ι v, hv⟩).symm
    · intro g' _ hg'
      have hv : (a ∘ ι) v ≠ g' := Ne.symm hg'
      simp only [L, N, mul_groupInclusion, dif_neg hv, add_zero]
    · simp
  have hL (g : G) :
      (L g).rank ≤ min (Fintype.card (GroupFiber (a ∘ ι) g)) (Fintype.card (GroupFiber b g)) := by
    have h : (L g).rank ≤ (B g).rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    exact h.trans (le_min (B g).rank_le_card_width (B g).rank_le_card_height)
  have hN (g : G) : (N g).rank ≤ (restrictGroupMatrix ι a g (C g)).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  calc
    (A.submatrix id ι).rank = (∑ g, (L g + N g)).rank := congrArg Matrix.rank hdecomp
    _ ≤ ∑ g, (L g + N g).rank := rank_sum_bound Finset.univ _
    _ ≤ ∑ g, ((restrictGroupMatrix ι a g (C g)).rank +
        min (Fintype.card (GroupFiber (a ∘ ι) g)) (Fintype.card (GroupFiber b g))) :=
      Finset.sum_le_sum (fun g _ =>
        (rank_add_bound (L g) (N g)).trans (by simpa [Nat.add_comm] using Nat.add_le_add (hL g) (hN g)))
    _ = _ := Finset.sum_add_distrib

private theorem sum_card_groupFiber {U G : Type*} [Fintype U] [Fintype G]
    [DecidableEq G] (a : U → G) :
    (∑ g, Fintype.card (GroupFiber a g)) = Fintype.card U := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv a)

private theorem twice_min_add_abs_diff (a b : ℕ) :
    2 * min a b + Int.natAbs ((a : ℤ) - b) = a + b := by
  omega

private theorem two_mul_sum_min_add_imbalance {U G : Type*} [Fintype U] [Fintype G]
    [DecidableEq G] (a b : U → G) :
    2 * (∑ g, min (Fintype.card (GroupFiber a g)) (Fintype.card (GroupFiber b g))) +
        twiceImbalance a b = 2 * Fintype.card U := by
  rw [twiceImbalance, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [twice_min_add_abs_diff]
  rw [Finset.sum_add_distrib, sum_card_groupFiber a, sum_card_groupFiber b, two_mul]

/-- The principal restriction in equation (3), stated for an arbitrary finite
index type of selected incidences. This is equation (3) multiplied by two. -/
theorem imbalance_of_selected_rows {V U I G : Type*} [Fintype U] [DecidableEq U]
    [Fintype G] [DecidableEq G] {M : I → G → Type*} [∀ t g, Fintype (M t g)]
    (ι : U → V) (T : Finset I) (node : I → F) (R : ℕ)
    (a : I → V → G) (b : I → U → G)
    (P : Matrix U V F[X]) (C : ∀ t g, Matrix (M t g) (GroupFiber (a t) g) F)
    (hnodes : Set.InjOn node (↑T : Set I))
    (hzero : (P.submatrix id ι).map (Polynomial.eval 0) = 1)
    (hdegree : ∀ u v, (P u v).natDegree ≤ R)
    (hforeign : ∀ t ∈ T, ∀ u g, b t u ≠ g →
      (fun v : GroupFiber (a t) g => (P u v.val).eval (node t)) ∈
        Submodule.span F (Set.range (C t g).row)) :
    (∑ t : T, twiceImbalance (a t ∘ ι) (b t)) ≤
      2 * ((∑ t : T, measurementRank ι (a t) (C t)) + R * Fintype.card U) := by
  classical
  let Q : Matrix U U F[X] := P.submatrix id ι
  let nullity (t : T) := Fintype.card U - (Q.map (Polynomial.eval (node t))).rank
  have hbudget : (∑ t : T, nullity t) ≤ Fintype.card U * R :=
    normalized_nullity_budget Q (fun t : T => node t) R
      (fun t t' h => Subtype.ext (hnodes t.property t'.property h)) hzero
      (fun u v => hdegree u (ι v))
  have hpoint (t : T) : twiceImbalance (a t ∘ ι) (b t) ≤
      2 * (measurementRank ι (a t) (C t) + nullity t) := by
    have hr := restricted_rank_le ι (a t) (b t) (P.map (Polynomial.eval (node t)))
      (C t) (hforeign t t.property)
    change (Q.map (Polynomial.eval (node t))).rank ≤ _ at hr
    have himb := two_mul_sum_min_add_imbalance (a t ∘ ι) (b t)
    have hrank := (Q.map (Polynomial.eval (node t))).rank_le_card_width
    dsimp [nullity]
    omega
  calc
    _ ≤ ∑ t : T, 2 * (measurementRank ι (a t) (C t) + nullity t) :=
      Finset.sum_le_sum (fun t _ => hpoint t)
    _ = 2 * ((∑ t : T, measurementRank ι (a t) (C t)) + ∑ t : T, nullity t) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left 2 (Nat.add_le_add_left (by simpa [Nat.mul_comm] using hbudget) _)

/-- Theorem 1 for the incidence model of equation (1). Fix one incident
factor for each variable of `V₀`; then restrict both physical axes to any
`U` inside `V₀`, with any set `T` of nodes. The conclusion is equation (3)
with both sides multiplied by two, so every quantity is a natural number. -/
theorem principal_subset_imbalance {V I G Factor : Type*} [DecidableEq V]
    [Fintype G] [DecidableEq G] {M : I → G → Type*} [∀ t g, Fintype (M t g)]
    (V₀ : Finset V) (U : Finset V₀) (T : Finset I) (node : I → F) (R : ℕ)
    (a : I → V → G) (b : I → Factor → G) (scope : Factor → V → Prop)
    (chosen : V₀ → Factor) (hchosen : ∀ v : V₀, scope (chosen v) v.val)
    (P : Factor → V → V → F[X])
    (C : ∀ t g, Matrix (M t g) (GroupFiber (a t) g) F)
    (hnodes : Set.InjOn node (↑T : Set I))
    (hzero : ∀ f v, scope f v → ∀ w, (P f v w).eval 0 = if v = w then 1 else 0)
    (hdegree : ∀ f v, scope f v → ∀ w, (P f v w).natDegree ≤ R)
    (hforeign : ∀ t ∈ T, ∀ f v, scope f v → ∀ g, b t f ≠ g →
      (fun w : GroupFiber (a t) g => (P f v w.val).eval (node t)) ∈
        Submodule.span F (Set.range (C t g).row)) :
    (∑ t : T, twiceImbalance (fun u : U => a t u.val.val) (fun u : U => b t (chosen u.val))) ≤
      2 * ((∑ t : T, measurementRank (fun u : U => u.val.val) (a t) (C t)) + R * U.card) := by
  let ι (u : U) : V := u.val.val
  let A : Matrix U V F[X] := Matrix.of (fun u w => P (chosen u.val) (ι u) w)
  have hA0 : (A.submatrix id ι).map (Polynomial.eval 0) = 1 := by
    ext u w
    have hi : ι u = ι w ↔ u = w :=
      ⟨fun h => Subtype.ext (Subtype.ext h), congrArg ι⟩
    simp only [A, Matrix.map_apply, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
      Matrix.one_apply]
    simpa only [hi] using hzero (chosen u.val) (ι u) (hchosen u.val) (ι w)
  simpa only [Fintype.card_coe] using
    imbalance_of_selected_rows ι T node R a (fun t u => b t (chosen u.val)) A C hnodes hA0
      (fun u w => hdegree _ _ (hchosen u.val) w)
      (fun t ht u g hg => hforeign t ht _ _ (hchosen u.val) g hg)

end
end LayoutBudget
end Reconstruction
