import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.BigOperators

/-!
# Matrix rank of a sum of separated functions

The full assignments on the two sides of a matching transversal form the rows
and columns of one matrix. Each summand may partition these endpoints
differently. Conditioning the smaller pair of row and column restrictions
gives an explicit factorization for that summand in the original coordinates.
-/

namespace SeparatedRank

open scoped BigOperators

/-- Conditioning a row state and a column state gives a factorization through
their product. The row and column maps may be arbitrary. -/
theorem conditioned_rank {R C X Y K : Type*} [Fintype C] [Fintype X] [Fintype Y]
    [Field K] (p : R → X) (q : C → Y) (F : R → Y → K) (G : X → C → K) :
    (Matrix.of fun r c => F r (q c) * G (p r) c).rank ≤ Fintype.card X * Fintype.card Y := by
  classical
  let L : Matrix R (X × Y) K := fun r u => if u.1 = p r then F r u.2 else 0
  let H : Matrix (X × Y) C K := fun u c => if u.2 = q c then G u.1 c else 0
  have hfac : (Matrix.of fun r c => F r (q c) * G (p r) c) = L * H := by
    ext r c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp [L, H, mul_ite, ite_mul]
  rw [hfac]
  simpa using (Matrix.rank_mul_le_left L H).trans L.rank_le_card_width

/-- Rank is subadditive for matrices over a field. -/
theorem rank_add_le {R C K : Type*} [Fintype R] [Fintype C] [Field K]
    (A B : Matrix R C K) : (A + B).rank ≤ A.rank + B.rank := by
  change Module.finrank K (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank K (LinearMap.range A.mulVecLin) + Module.finrank K (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin))

/-- Rank is subadditive term by term, including empty sums. -/
theorem rank_sum_le {R C J K : Type*} [Fintype R] [Fintype C] [Field K]
    (s : Finset J) (M : J → Matrix R C K) :
    (∑ j ∈ s, M j).rank ≤ ∑ j ∈ s, (M j).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- The two finite sets pick the row and column endpoints lying in the same
side of the separation. The remaining endpoints feed the other function. -/
structure CutTerm (ι K : Type*) [Fintype ι] [DecidableEq ι] where
  rowPart : Finset ι
  colPart : Finset ι
  coeff : K
  onCut : (rowPart → Bool) → (colPart → Bool) → K
  offCut : ((rowPartᶜ : Finset ι) → Bool) → ((colPartᶜ : Finset ι) → Bool) → K

namespace CutTerm

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]

/-- Restrict a full endpoint assignment to the indicated subset. -/
def restrict (s : Finset ι) (x : ι → Bool) : s → Bool := fun i => x i

/-- A signed scalar times the product of the two group-local functions. -/
def matrix [Mul K] (t : CutTerm ι K) : Matrix (ι → Bool) (ι → Bool) K :=
  Matrix.of fun r c =>
    t.coeff * t.onCut (restrict t.rowPart r) (restrict t.colPart c) *
      t.offCut (restrict t.rowPartᶜ r) (restrict t.colPartᶜ c)

/-- Natural-valued absolute difference of the two endpoint counts. -/
def imbalance (t : CutTerm ι K) : ℕ :=
  (t.rowPart.card - t.colPart.card) + (t.colPart.card - t.rowPart.card)

theorem imbalance_le (t : CutTerm ι K) : t.imbalance ≤ Fintype.card ι := by
  have ha := Finset.card_le_univ t.rowPart
  have hb := Finset.card_le_univ t.colPart
  unfold imbalance
  omega

/-- Equation (E). Each of the two possible orientations conditions a smaller
pair of restrictions; both factorizations use the common full-coordinate matrix. -/
theorem rank_le [Field K] (t : CutTerm ι K) :
    t.matrix.rank ≤ 2 ^ (Fintype.card ι - t.imbalance) := by
  classical
  have ha := Finset.card_le_univ t.rowPart
  have hb := Finset.card_le_univ t.colPart
  by_cases hab : t.colPart.card ≤ t.rowPart.card
  · have h := conditioned_rank (restrict t.rowPartᶜ) (restrict t.colPart)
        (fun r y => t.coeff * t.onCut (restrict t.rowPart r) y)
        (fun x c => t.offCut x (restrict t.colPartᶜ c))
    change t.matrix.rank ≤ _ at h
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Finset.card_compl,
      ← pow_add, show Fintype.card ι - t.rowPart.card + t.colPart.card =
          Fintype.card ι - t.imbalance by unfold imbalance; omega] using h
  · have h := conditioned_rank (restrict t.rowPart) (restrict t.colPartᶜ)
        (fun r y => t.offCut (restrict t.rowPartᶜ r) y)
        (fun x c => t.coeff * t.onCut x (restrict t.colPart c))
    have hfac : (Matrix.of fun r c =>
        t.offCut (restrict t.rowPartᶜ r) (restrict t.colPartᶜ c) *
          (t.coeff * t.onCut (restrict t.rowPart r) (restrict t.colPart c))) = t.matrix := by
      ext r c
      exact mul_comm _ _
    rw [hfac] at h
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Finset.card_compl,
      ← pow_add, show t.rowPart.card + (Fintype.card ι - t.colPart.card) =
          Fintype.card ι - t.imbalance by unfold imbalance; omega] using h

end CutTerm

variable {ι J K : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Field K]

/-- Before replacing all deficits by a common lower bound, retain the
individual capacity of every separated term. -/
theorem separated_rank_sum (terms : J → CutTerm ι K) :
    (∑ j, (terms j).matrix).rank ≤ ∑ j, 2 ^ (Fintype.card ι - (terms j).imbalance) :=
  (rank_sum_le Finset.univ (fun j => (terms j).matrix)).trans
    (Finset.sum_le_sum fun j _ => (terms j).rank_le)

/-- A full-rank Boolean transversal forces at least `2^d` entrances whenever
every summand's own cut has endpoint imbalance at least `d`. -/
theorem separated_barrier (terms : J → CutTerm ι K) (M : Matrix (ι → Bool) (ι → Bool) K)
    (hfull : M.rank = 2 ^ Fintype.card ι) (hsum : M = ∑ j, (terms j).matrix)
    (d : ℕ) (hgap : ∀ j, d ≤ (terms j).imbalance) : 2 ^ d ≤ Fintype.card J := by
  classical
  have hcap := separated_rank_sum terms
  rw [← hsum, hfull] at hcap
  cases isEmpty_or_nonempty J with
  | inl h => simp at hcap
  | inr h =>
    have hdm : d ≤ Fintype.card ι := (hgap h.some).trans (terms h.some).imbalance_le
    have hs : 2 ^ Fintype.card ι ≤ Fintype.card J * 2 ^ (Fintype.card ι - d) := by
      refine hcap.trans ?_
      calc
        _ ≤ ∑ _j : J, 2 ^ (Fintype.card ι - d) := Finset.sum_le_sum fun j _ =>
          Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left (hgap j) _)
        _ = _ := by simp
    have hpow : 2 ^ d * 2 ^ (Fintype.card ι - d) = 2 ^ Fintype.card ι := by
      rw [← pow_add, Nat.add_sub_of_le hdm]
    exact Nat.le_of_mul_le_mul_right (hpow ▸ hs) (Nat.two_pow_pos _)

/-- An arbitrary coefficient and two functions of the two sides of a cut of
the original vertex signs, before restricting to a matching. -/
structure VertexTerm (V K : Type*) [Fintype V] [DecidableEq V] where
  side : Finset V
  coeff : K
  onCut : (side → Bool) → K
  offCut : ((sideᶜ : Finset V) → Bool) → K

section VertexRestriction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Place the row/column values at the false/true endpoints and set every
other vertex sign to true. -/
noncomputable def pinnedSigns (e : (ι × Bool) ↪ V) (x y : ι → Bool) : V → Bool :=
  Function.extend e (fun p => if p.2 then y p.1 else x p.1) (fun _ => true)

/-- Matched indices whose indicated endpoint lies in a vertex cut. -/
def endpointPart (e : (ι × Bool) ↪ V) (s : Finset V) (b : Bool) : Finset ι :=
  Finset.univ.filter fun i => e (i, b) ∈ s

/-- The absolute difference in endpoint counts, read directly on the original
vertex cut. -/
def endpointImbalance (e : (ι × Bool) ↪ V) (s : Finset V) : ℕ :=
  let a := (endpointPart e s false).card
  let b := (endpointPart e s true).card
  (a - b) + (b - a)

namespace VertexTerm

/-- Evaluation on an unrestricted vertex assignment. -/
def value (t : VertexTerm V K) (σ : V → Bool) : K :=
  t.coeff * t.onCut (CutTerm.restrict t.side σ) * t.offCut (CutTerm.restrict t.sideᶜ σ)

private def fill (s : Finset ι) (x : s → Bool) (i : ι) : Bool :=
  if hi : i ∈ s then x ⟨i, hi⟩ else true

private noncomputable def view (e : (ι × Bool) ↪ V) (s : Finset V) (a b : Finset ι)
    (x : a → Bool) (y : b → Bool) : s → Bool :=
  CutTerm.restrict s (pinnedSigns e (fill a x) (fill b y))

omit [Fintype V] in
/-- A vertex view may discard every matching endpoint outside that view. -/
private theorem view_restrict (e : (ι × Bool) ↪ V) (s : Finset V) (a b : Finset ι)
    (ha : ∀ i, e (i, false) ∈ s → i ∈ a) (hb : ∀ i, e (i, true) ∈ s → i ∈ b)
    (x y : ι → Bool) :
    view e s a b (CutTerm.restrict a x) (CutTerm.restrict b y) =
      CutTerm.restrict s (pinnedSigns e x y) := by
  classical
  funext v
  unfold view CutTerm.restrict pinnedSigns
  by_cases hv : ∃ p, e p = v.val
  · obtain ⟨⟨i, c⟩, he⟩ := hv
    have hs : e (i, c) ∈ s := he ▸ v.property
    rw [← he, e.injective.extend_apply, e.injective.extend_apply]
    cases c
    · simp [fill, ha i hs]
    · simp [fill, hb i hs]
  · rw [Function.extend_apply' _ _ _ hv, Function.extend_apply' _ _ _ hv]

/-- Specialize both arbitrary functions of a vertex term to just the matching
endpoint coordinates visible on their respective sides. -/
noncomputable def onTransversal (t : VertexTerm V K) (e : (ι × Bool) ↪ V) : CutTerm ι K :=
  let a := endpointPart e t.side false
  let b := endpointPart e t.side true
  { rowPart := a
    colPart := b
    coeff := t.coeff
    onCut := fun x y => t.onCut (view e t.side a b x y)
    offCut := fun x y => t.offCut (view e t.sideᶜ aᶜ bᶜ x y) }

/-- The specialized matrix agrees entrywise with the original product on
the actual pinned vertex assignments. -/
theorem onTransversal_apply (t : VertexTerm V K) (e : (ι × Bool) ↪ V) (x y : ι → Bool) :
    (t.onTransversal e).matrix x y = t.value (pinnedSigns e x y) := by
  let a := endpointPart e t.side false
  let b := endpointPart e t.side true
  have hon := view_restrict e t.side a b
    (by intro i hi; simpa [a, endpointPart] using hi)
    (by intro i hi; simpa [b, endpointPart] using hi) x y
  have hoff := view_restrict e t.sideᶜ aᶜ bᶜ
    (by intro i hi; simpa [a, endpointPart] using hi)
    (by intro i hi; simpa [b, endpointPart] using hi) x y
  exact congrArg₂ (fun u v => t.coeff * t.onCut u * t.offCut v) hon hoff

end VertexTerm

/-- The original vertex-wise output representation implies a decomposition of
the restricted matrix, even when every entrance uses its own original cut. -/
theorem vertex_restriction_sum (terms : J → VertexTerm V K) (B : (V → Bool) → K)
    (hvalue : ∀ σ, B σ = ∑ j, (terms j).value σ) (e : (ι × Bool) ↪ V) :
    (Matrix.of fun x y => B (pinnedSigns e x y)) = ∑ j, ((terms j).onTransversal e).matrix := by
  ext x y
  rw [Matrix.of_apply, Matrix.sum_apply]
  simpa only [VertexTerm.onTransversal_apply] using hvalue (pinnedSigns e x y)

/-- The entrance bound stated directly for products separated on the original
vertex signs, with all cut deficits computed from one endpoint embedding. -/
theorem vertex_barrier (terms : J → VertexTerm V K) (B : (V → Bool) → K)
    (hvalue : ∀ σ, B σ = ∑ j, (terms j).value σ) (e : (ι × Bool) ↪ V)
    (hfull : (Matrix.of fun x y => B (pinnedSigns e x y)).rank = 2 ^ Fintype.card ι)
    (d : ℕ) (hgap : ∀ j, d ≤ endpointImbalance e (terms j).side) :
    2 ^ d ≤ Fintype.card J :=
  separated_barrier (fun j => (terms j).onTransversal e) _ hfull
    (vertex_restriction_sum terms B hvalue e) d hgap

end VertexRestriction

#print axioms conditioned_rank
#print axioms rank_add_le
#print axioms rank_sum_le
#print axioms CutTerm.imbalance_le
#print axioms CutTerm.rank_le
#print axioms separated_rank_sum
#print axioms separated_barrier
#print axioms VertexTerm.onTransversal_apply
#print axioms vertex_restriction_sum
#print axioms vertex_barrier

end SeparatedRank
