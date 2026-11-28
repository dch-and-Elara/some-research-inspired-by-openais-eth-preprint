import V8PooledRangeSplit
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace V8PooledRange
namespace Split

noncomputable def endpointRange {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) : Finset ℕ :=
  Finset.univ.image (fun x : Word k × Bool =>
    satCount (graph H p) (ports H p) (hostEnabled k x.1 x.2))

/-- The recurrence range is literally realized by counts of the original
five-copy clauses. Each side of a pair may use a different switch input. -/
theorem endpoint_range_agrees {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) :
    endpointRange H p = CaterpillarRange.attained k := by
  unfold endpointRange CaterpillarRange.attained
  congr 1
  funext x
  exact exact_endpoint H p x.1 x.2

theorem endpoint_range_square {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) :
    2^k ≤ (endpointRange H p).card^2 := by
  rw [endpoint_range_agrees]
  exact CaterpillarRange.output_range_square k

private theorem logb_lower_of_square (k n : ℕ) (h : 2^k ≤ n^2) :
    (k : ℝ)/2 ≤ Real.logb 2 (n : ℝ) := by
  have h' : (2:ℝ)^k ≤ (n:ℝ)^2 := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity : 0 < (2:ℝ)^k) h'
  rw [Real.log_pow,Real.log_pow] at hlog
  have hp := Real.log_pos (by norm_num : (1:ℝ) < 2)
  unfold Real.logb
  apply (le_div_iff₀ hp).mpr
  norm_num at hlog
  nlinarith

theorem c6_endpoint_log_range {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) :
    ((Fintype.card (V k) : ℝ)-10)/12 ≤ Real.logb 2 ((endpointRange H p).card : ℝ) := by
  have h := logb_lower_of_square k (endpointRange H p).card (endpoint_range_square H p)
  rw [order]
  push_cast
  linarith

theorem c6_full_log_range {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) :
    ((Fintype.card (V k) : ℝ)-10)/12 ≤ Real.logb 2 ((physicalRange (graph H p) (ports H p)).card : ℝ) := by
  have h := logb_lower_of_square k _ (exact_range H p)
  rw [order]
  push_cast
  linarith

def collideOffA : Word 4 := fun i => decide (i=1 ∨ i=3)
def collideOffB : Word 4 := fun i => decide (i=1 ∨ i=2)
def collideOnA : Word 3 := fun i => decide (i=0 ∨ i=2)
def collideOnB : Word 3 := fun i => decide (i=0 ∨ i=1)

/-- Individual endpoint-off observations on a true fixed physical graph
are not an injective code for the word, despite pair injectivity. -/
theorem exact_off_collision {E : Type*} (H : Graph (Deficit 4) E) (p : ThreePorts H) :
    collideOffA ≠ collideOffB ∧
    satCount (graph H p) (ports H p) (hostEnabled 4 collideOffA false) = 108 ∧
    satCount (graph H p) (ports H p) (hostEnabled 4 collideOffB false) = 108 ∧
    satCount (graph H p) (ports H p) (hostEnabled 4 collideOffA true) = 192 ∧
    satCount (graph H p) (ports H p) (hostEnabled 4 collideOffB true) = 186 := by
  simp only [exact_endpoint]
  decide

/-- The complementary fixed on-endpoint can collide as well. -/
theorem exact_on_collision {E : Type*} (H : Graph (Deficit 3) E) (p : ThreePorts H) :
    collideOnA ≠ collideOnB ∧
    satCount (graph H p) (ports H p) (hostEnabled 3 collideOnA true) = 108 ∧
    satCount (graph H p) (ports H p) (hostEnabled 3 collideOnB true) = 108 ∧
    satCount (graph H p) (ports H p) (hostEnabled 3 collideOnA false) = 84 ∧
    satCount (graph H p) (ports H p) (hostEnabled 3 collideOnB false) = 78 := by
  simp only [exact_endpoint]
  decide

#print axioms endpoint_range_agrees
#print axioms endpoint_range_square
#print axioms c6_endpoint_log_range
#print axioms c6_full_log_range
#print axioms exact_off_collision
#print axioms exact_on_collision

end Split
end V8PooledRange
