import J6R11CollisionGreedy

/-! The collision guarantee applies to every sequence of minimizing choices. -/
namespace Paper5.RootGreedy
open scoped BigOperators Classical
open J6R11Collision J6R11CollisionGreedy GuardExpectation DiagonalAbundance
noncomputable section
set_option maxHeartbeats 3000000
variable {E R C A : Type*} [Fintype E] [Fintype R] [Fintype C] [Fintype A]
  [Nonempty A]
variable (row : E → R) (col : E → C)

abbrev weights (z : R ⊕ C → A) (s : Finset (R ⊕ C)) :=
  fixOn (fun _ _ => (Fintype.card A:ℚ)⁻¹) s z

omit [Fintype R] [Fintype C] in
private theorem weights_nonnegative (z : R ⊕ C → A) (s : Finset (R ⊕ C)) (i b) :
    0 ≤ weights z s i b := by
  simp only [weights,fixOn,indicator]
  split <;> positivity

omit [Fintype R] [Fintype C] in
private theorem weights_normalized (z : R ⊕ C → A) (s : Finset (R ⊕ C)) (i) :
    ∑ b, weights z s i b = 1 := by
  by_cases hi : i∈s
  · simp [weights,fixOn,hi,indicator]
  · simp [weights,fixOn,hi,nsmul_eq_mul]

omit [Fintype R] [Fintype C] [Nonempty A] in
private theorem insert_weights (z : R ⊕ C → A) (s : Finset (R ⊕ C)) (i : R ⊕ C) :
    weights z (insert i s) = fixAt (weights z s) i (z i) := by
  funext j b
  by_cases h : j=i
  · subst j; simp [weights,fixOn,fixAt]
  · simp [weights,fixOn,fixAt,h]

/-- A transcript fixes a new vertex to any label minimizing the literal
ordered-pair score. The order of the unfixed vertices is unrestricted. -/
inductive Prefix (z : R ⊕ C → A) : Finset (R ⊕ C) → Prop
  | empty : Prefix z ∅
  | step {s i} : Prefix z s → i∉s →
      (∀ b, compressed row col (fixAt (weights z s) i (z i)) ≤
        compressed row col (fixAt (weights z s) i b)) →
      Prefix z (insert i s)

theorem every_prefix_nonincreasing (z : R ⊕ C → A) {s} (p : Prefix row col z s) :
    compressed row col (weights z s) ≤ compressed row col (weights z ∅) := by
  induction p with
  | empty => exact le_rfl
  | @step s i _ _ hmin ih =>
    obtain ⟨b,h⟩ := greedy_step row col (weights z s) (weights_nonnegative z s)
      (weights_normalized z s) i
    rw [insert_weights]
    exact ((hmin b).trans h).trans ih

/-- A completed minimizing transcript obeys the same graph bound regardless
of the coordinate order and of every tie. -/
theorem every_full_transcript_collision (Δ : ℕ)
    (hr : ∀ v,(fibre row v).card≤Δ) (hc : ∀ v,(fibre col v).card≤Δ)
    (z : R ⊕ C → A) (p : Prefix row col z Finset.univ) :
    J1MainSourceCollision.deviation (edgeCell row col (splitSample z)) ≤
      2*(Fintype.card E:ℚ)*Δ := by
  let G := fun y : Sample R C A => J1MainSourceCollision.deviation (edgeCell row col y)
  let F := fun x : R ⊕ C → A => G (splitSample x)
  have h := every_prefix_nonincreasing row col z p
  rw [←compressed_correct row col _ (weights_normalized z Finset.univ),
      ←compressed_correct row col _ (weights_normalized z ∅)] at h
  change average (weights z Finset.univ) F ≤ average (weights z ∅) F at h
  rw [weights,average_fixOn_univ] at h
  have hw : weights z ∅ = fun _ _ => (Fintype.card A:ℚ)⁻¹ := by
    funext i b; simp [weights,fixOn]
  rw [hw,uniform_product_mean] at h
  exact h.trans ((mean_equiv splitSample G).le.trans (expected_squared_loads row col Δ hr hc))

#print axioms every_prefix_nonincreasing
#print axioms every_full_transcript_collision
end
end Paper5.RootGreedy
