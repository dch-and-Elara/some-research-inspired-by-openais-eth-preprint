import S8PrefixScore
import S8DoubleSampling

namespace S8.Prefix

open scoped BigOperators
open ProductVariance

variable {P A W X R I : Type*} [Fintype P] [DecidableEq P] [Fintype A] [DecidableEq A]
  [Nonempty A] [Fintype W] [DecidableEq X] [Fintype X] [Fintype R] [Fintype I]

def pairTest (loc : W → X → P) (p : W × W) : Test P A :=
  agreement (loc p.1) (loc p.2)

theorem pairTest_sum (loc : W → X → P) (ω : P → A) :
    rawScore (pairTest loc) (fun _ => 1) ω =
      collision (fun w => ω ∘ loc w) + (Fintype.card W : ℚ)^2 / Fintype.card (X → A) := by
  simp only [rawScore, pairTest, Nat.cast_one, one_mul, agreement_indicator,
    Fintype.sum_prod_type, collision_pair, sub_add_cancel]

theorem conditional_all (f : (P → A) → ℚ) (order : List P) (cover : ∀ p, p ∈ order)
    (fixed : P → A) : conditional f order fixed = uniformMean f := by
  have h (x : P → A) : complete order fixed x = x := by
    funext p
    exact if_pos (cover p)
  simp only [conditional, h]

theorem mean_add_const (f : (P → A) → ℚ) (c : ℚ) :
    uniformMean (fun x => f x + c) = uniformMean f + c := by
  have h : (∑ _ : P → A, uniformWeight (P → A)) = 1 := uniform_mass
  simp only [uniformMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h ⊢
  rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = uniformWeight (P → A) * (∑ x, f x) +
      ((Fintype.card (P → A) : ℚ) * uniformWeight (P → A)) * c := by ring
    _ = _ := by rw [h, one_mul]

def collisionSolve (loc : W → X → P) (enumeration : List P) (symbols : List A) (zero : A) :
    P → A :=
  solve (score (pairTest loc) (fun _ => 1) (2*Fintype.card X)) symbols zero enumeration (fun _ => zero)

theorem collisionSolve_le (loc : W → X → P) (order : List P) (on : order.Nodup) (oc : ∀ p, p ∈ order)
    (symbols : List A) (sc : ∀ a, a ∈ symbols) (zero : A) :
    collision (fun w => collisionSolve loc order symbols zero ∘ loc w) ≤
      uniformMean (fun ω : P → A => collision (fun w => ω ∘ loc w)) := by
  have h := solve_score_le (pairTest loc) (fun _ => 1) (2*Fintype.card X)
    (fun p => agreement_width (loc p.1) (loc p.2)) symbols sc zero order on (fun _ => zero)
  rw [conditional_all _ _ oc] at h
  change rawScore (pairTest loc) (fun _ => 1) (collisionSolve loc order symbols zero) ≤
    uniformMean (rawScore (pairTest loc) (fun _ => 1)) at h
  rw [pairTest_sum] at h
  have hh := congrArg uniformMean (funext (fun ω : P → A => pairTest_sum loc ω))
  rw [mean_add_const] at hh
  rw [hh] at h
  exact le_of_add_le_add_right h

abbrev MainTerm (W I R : Type*) := (W × W) ⊕ (I × R × R)

def mainTest (loc : W → X → P) (var : I → R → P) : MainTerm W I R → Test P A
  | .inl p => pairTest loc p
  | .inr (i,u,v) => agreement (fun _ : Unit => var i u) (fun _ => var i v)

def mainWeight (M Q n : ℕ) : MainTerm W I R → ℕ
  | .inl _ => Q*n
  | .inr _ => 5*M

def phi (loc : W → X → P) (ω : P → A) : ℚ :=
  collision (fun w => ω ∘ loc w)

def xi (var : I → R → P) (ω : P → A) : ℚ :=
  ∑ i, collision (fun u => ω (var i u))

def joint (loc : W → X → P) (var : I → R → P) (ω : P → A) : ℚ :=
  (Fintype.card I : ℚ) * Fintype.card R * phi loc ω +
    5 * Fintype.card W * xi var ω

def mainOffset : ℚ :=
  ((Fintype.card I : ℚ) * Fintype.card R) *
    ((Fintype.card W : ℚ)^2 / (Fintype.card (X → A) : ℚ)) +
  (5 * Fintype.card W : ℚ) * ((Fintype.card I : ℚ) * ((Fintype.card R : ℚ)^2 / Fintype.card A))

theorem main_eq_joint (loc : W → X → P) (var : I → R → P) (ω : P → A) :
    rawScore (mainTest loc var) (mainWeight (Fintype.card W) (Fintype.card I) (Fintype.card R)) ω =
      joint loc var ω + mainOffset (W := W) (I := I) (R := R) (X := X) (A := A) := by
  classical
  simp only [rawScore, Fintype.sum_sum_type, mainWeight, mainTest,
    Nat.cast_mul, Nat.cast_ofNat, ← Finset.mul_sum]
  have hL : (∑ x : W × W, (pairTest loc x).indicator ω) =
      phi loc ω + (Fintype.card W : ℚ)^2 / Fintype.card (X → A) := by
    simpa only [rawScore, Nat.cast_one, one_mul, phi] using pairTest_sum loc ω
  have hR (i : I) :
      (∑ u : R, ∑ v : R, (agreement (fun _ : Unit => var i u) (fun _ => var i v)).indicator ω) =
        collision (fun u : R => ω (var i u)) + (Fintype.card R : ℚ)^2 / Fintype.card A := by
    simp only [agreement_indicator, Function.comp_def, funext_iff, forall_const,
      collision_pair, sub_add_cancel]
  rw [hL, Fintype.sum_prod_type (f := fun x : I × R × R =>
    (agreement (fun _ : Unit => var x.1 x.2.1) (fun _ => var x.1 x.2.2)).indicator ω)]
  simp only [Fintype.sum_prod_type, hR, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, joint, xi, mainOffset]
  ring

def mainSolve (loc : W → X → P) (var : I → R → P)
    (order : List P) (symbols : List A) (zero : A) : P → A :=
  solve (score (mainTest loc var) (mainWeight (Fintype.card W) (Fintype.card I) (Fintype.card R))
    (2*Fintype.card X)) symbols zero order (fun _ => zero)

theorem mainSolve_le (loc : W → X → P) (var : I → R → P) (hx : 0 < Fintype.card X)
    (order : List P) (on : order.Nodup) (oc : ∀ p, p ∈ order)
    (symbols : List A) (sc : ∀ a, a ∈ symbols) (zero : A) :
    joint loc var (mainSolve loc var order symbols zero) ≤ uniformMean (fun ω : P → A => joint loc var ω) := by
  have hbound (j : MainTerm W I R) : (mainTest (A := A) loc var j).support.card ≤
      2 * Fintype.card X := by
    cases j with
    | inl j => exact agreement_width _ _
    | inr j =>
      obtain ⟨i,u,v⟩ := j
      exact (agreement_width (A := A) (fun _ : Unit => var i u) (fun _ => var i v)).trans (by simpa using hx)
  have h := solve_score_le (mainTest (A := A) loc var)
    (mainWeight (Fintype.card W) (Fintype.card I) (Fintype.card R)) _ hbound symbols sc zero order on (fun _ => zero)
  rw [conditional_all _ _ oc] at h
  change rawScore (mainTest loc var) _ (mainSolve loc var order symbols zero) ≤ _ at h
  rw [main_eq_joint] at h
  have hh := congrArg uniformMean (funext (fun ω : P → A => main_eq_joint loc var ω))
  rw [mean_add_const] at hh
  rw [hh] at h
  exact le_of_add_le_add_right h

#print axioms collisionSolve_le
#print axioms main_eq_joint
#print axioms mainSolve_le

end S8.Prefix
