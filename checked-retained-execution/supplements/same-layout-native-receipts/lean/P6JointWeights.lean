import P6JointSignedQuota
import P6JointReserve

namespace Paper6JointSeating
open scoped BigOperators
open GuardedPacking

def ofCell {W C : Type*} [DecidableEq C]
    (label : W → C) (s : Finset W) (c : C) : Finset W :=
  s.filter fun w => label w = c

def weights {W C E : Type*} [DecidableEq C] [DecidableEq E]
    (label : W → C) (own : W → E) (s : Finset W)
    (e : E) (c : C) : ℕ := ((ofCell label s c).filter fun w => own w=e).card

theorem load_filter {W C E : Type*} [DecidableEq C] [DecidableEq E]
    (label : W → C) (own : W → E) (s : Finset W)
    (keep : Finset E) (c : C) :
    cellLoad (weights label own s) keep c = ((ofCell label s c).filter fun w => own w ∈ keep).card := by
  unfold cellLoad weights
  simp only [Finset.card_eq_sum_ones]
  exact Finset.sum_fiberwise_eq_sum_filter (ofCell label s c) keep own (fun _ => 1)

theorem load_univ {W C E : Type*} [Fintype E] [DecidableEq C] [DecidableEq E]
    (label : W → C) (own : W → E) (s : Finset W) (c : C) :
    cellLoad (weights label own s) Finset.univ c = (ofCell label s c).card := by
  rw [load_filter]
  simp

theorem sum_cell {W C : Type*} [Fintype C] [DecidableEq C]
    (label : W → C) (s : Finset W) : (∑ c, (ofCell label s c).card) = s.card := by
  unfold ofCell
  simp only [Finset.card_eq_sum_ones]
  exact Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (label x)) (fun _ => 1)

theorem variance_le {W C E : Type*} [Fintype C] [Fintype E] [DecidableEq C] [DecidableEq E]
    (label : W → C) (own : W → E) (s : Finset W) (k : ℕ)
    (mult : ∀ e c, weights label own s e c ≤ k) :
    (∑ c, ∑ e, (weights label own s e c : ℝ)^2) ≤ k * (s.card : ℝ) := by
  have h (e : E) (c : C) : (weights label own s e c : ℝ)^2 ≤ k * (weights label own s e c : ℝ) := by
    have hk : (weights label own s e c : ℝ) ≤ k := by exact_mod_cast mult e c
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hk (by positivity)
  calc
    _ ≤ ∑ c, ∑ e, k * (weights label own s e c : ℝ) :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun e _ => h e c))
    _ = _ := by
      simp_rw [← Finset.mul_sum, ← Nat.cast_sum]
      change (k:ℝ) * ((∑ c, cellLoad (weights label own s) Finset.univ c : ℕ) : ℝ) = _
      simp_rw [load_univ, sum_cell]

#print axioms load_filter
#print axioms variance_le
end Paper6JointSeating

