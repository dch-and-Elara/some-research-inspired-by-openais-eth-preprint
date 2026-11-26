import P5H4Sharp
import P5H4WidthUpper

/-! Explicit sharpness and failure modes at the exact H4 interfaces:
uncaptured anchors, the actual factor width, and loss of naive point rank. -/
namespace P5H4
open Polynomial Matrix RankBudget
open scoped BigOperators Classical

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem allocated_eval_ne (s : Finset K) (k : K → ℕ) (t : K) (ht : t ∉ s) :
    (allocated s k).eval t ≠ 0 := by
  unfold allocated
  change (evalRingHom t) (∏ u ∈ s, (X-C u)^k u) ≠ 0
  rw [map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro u hu
  have h : t ≠ u := fun e => ht (e.symm ▸ hu)
  rw [map_pow]
  change (eval t (X-C u))^(k u) ≠ 0
  rw [eval_sub,eval_X,eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr h)

theorem allocated_anchor_regular (roots : Finset K) (k : K → ℕ) (a : K)
    (ha : a ∉ roots) :
    ((diagonal (fun _ : n => allocated roots k)).map (evalRingHom a)).det ≠ 0 := by
  rw [Matrix.diagonal_map (map_zero (evalRingHom a)),Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => allocated_eval_ne roots k a ha)

omit [DecidableEq n] in
theorem sharp_width_count (roots : Finset K) (k : K → ℕ) (t : K) :
    Fintype.card (Survivors (fun _ : n => allocated roots k) t (k t)) =
      if t ∈ roots ∨ k t = 0 then 0 else Fintype.card n := by
  unfold Survivors
  simp only [allocated_order]
  by_cases ht : t ∈ roots
  · simp [ht]
  · by_cases hk : k t = 0 <;> simp [ht,hk,Nat.pos_of_ne_zero]

/-- Equality in (H.4), using actual least widths, simultaneously with
the aggregate determinant- and image-defect equality of (H.6). -/
theorem actual_sharp_identity (s roots : Finset K) (hs : roots⊆s) (k : K → ℕ) :
    let A : Matrix n n K[X] := diagonal (fun _ => allocated roots k)
    let width (t : K) := Fintype.card (Survivors (fun _ : n => allocated roots k) t (k t))
    let d := ∑ t ∈ roots, k t
    (∑ t ∈ s, k t*(Fintype.card n-width t)) =
      (∑ t ∈ s, (Fintype.card n*k t-jetLength A t (k t))) ∧
      (∑ t ∈ s, (Fintype.card n*k t-jetLength A t (k t))) =
        A.det.natDegree ∧ A.det.natDegree = Fintype.card n*d ∧
      ∀ t, Factors ((X-C t)^k t) A (Survivors (fun _ : n => allocated roots k) t (k t)) := by
  dsimp only
  obtain ⟨_,hdeg,hdef⟩ := sharp_scalar_identity (n:=n) s roots hs k
  refine ⟨?_,hdef.trans hdeg.symm,hdeg,fun t =>
    diagonal_width_upper _ (fun _ => (allocated_monic _ _).ne_zero) t (k t)⟩
  apply Finset.sum_congr rfl
  intro t _
  rw [sharp_width_count]
  have hloc := (prescribed_diagonal (n:=n) roots (fun _ => k) t (k t)).2.2
  rw [hloc]
  by_cases ht : t ∈ roots
  · simp [ht,Nat.mul_comm]
  · by_cases hk : k t=0 <;> simp [ht,hk]

/-- Direct failure of the proposed multiplicity times point corank:
at 0, X I has rank zero, one surviving dimension per scalar jet
and determinant degree N. -/
theorem point_corank_counterexample [Nonempty n] :
    let A : Matrix n n K[X] := diagonal (fun _ => X)
    ((A.map (evalRingHom (0:K))).rank = 0) ∧
      RankBudget.jetLength A (0:K) 2 = Fintype.card n ∧
      A.det.natDegree = Fintype.card n ∧
      A.det.natDegree < 2*Fintype.card n := by
  dsimp only
  have hroot : rootMultiplicity (0:K) X=1 := by simpa using (rootMultiplicity_X_sub_C_self (x:=(0:K)))
  have hdeg : (diagonal (fun _ : n => (X : K[X]))).det.natDegree = Fintype.card n := by
    rw [Matrix.det_diagonal,natDegree_prod Finset.univ _ (fun _ _ => X_ne_zero)]
    simp
  refine ⟨?_,?_,hdeg,?_⟩
  · simp
  · rw [RankBudget.jetLength_diagonal _ (fun _ => X_ne_zero)]
    simp [hroot]
  · rw [hdeg]
    have hpos := Fintype.card_pos (α:=n)
    omega

#print axioms allocated_anchor_regular
#print axioms sharp_width_count
#print axioms actual_sharp_identity
#print axioms point_corank_counterexample
end P5H4
