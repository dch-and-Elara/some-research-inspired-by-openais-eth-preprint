import V8CapacityUnifiedRectangles
import V8CapacityUnifiedCut
import V8CapacityUnifiedMatching

/-! The original normalized U7/S6 bound: actual common matching
target, arbitrary signed fraction-field block values, the true
opposite-axis overlap fibers, and the cap at full square rank. -/
namespace V8CapacityUnified.U7
open scoped Classical BigOperators
open V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {O K B : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [Field K] [Algebra O K] [IsFractionRing O K] [Fintype B]

abbrev FiberMatrix {m : ℕ} (K : Type*) (c : Cut m) (f : Fiber c) :=
  Matrix {x // rowFiber c f x} {y // colFiber c f y} K

def assemble {m : ℕ} (c : Cut m) (a : (f : Fiber c) → FiberMatrix K c f) :
    Matrix (Bits m) (Bits m) K :=
  fiberSum (rowFiber c) (colFiber c) a

theorem assemble_rank {m : ℕ} (c : Cut m) (a : (f : Fiber c) → FiberMatrix K c f) (H : ℕ)
    (h : ∀ f, (a f).rank≤H) :
    (assemble c a).rank≤2^(m-c.delta+c.hazard)*H := by
  have hh := fiberSum_rank (rowFiber c) (colFiber c) a H h
  rw [c.fiber_card] at hh
  exact hh

theorem assemble_on {m : ℕ} (c : Cut m) (a : (f : Fiber c) → FiberMatrix K c f) (x y : Bits m) :
    assemble c a x y=a (fiberOf c x y) ⟨x,rfl⟩ ⟨y,rfl⟩ := by
  let f := fiberOf c x y
  have hr : rowFiber c f x := rfl
  have hc : colFiber c f y := rfl
  have other (g : Fiber c) (hg : g≠f) : ¬rowFiber c g x ∨ ¬colFiber c g y := by
    by_cases h : rowFiber c g x
    · right
      intro h'
      exact hg (((fiber_iff_eq c g x y).mp ⟨h,h'⟩).symm)
    · exact Or.inl h
  exact fiberSum_on (rowFiber c) (colFiber c) a x y f hr hc other

/-- A rank witness is required on every *actual* conditioned rectangle.
Neither an arbitrary new joint guard nor out-of-interface arithmetic is
thereby given a free capacity. Individual block values may be fractional. -/
def FiberCaps {m : ℕ} (π : O) (cuts : B → Cut m)
    (raw : B → Bits m → Bits m → K) (H : B → ℕ) : Prop :=
  ∀ b (f : Fiber (cuts b)),
    ∃ A : FiberMatrix K (cuts b) f,
      A.rank≤H b ∧ ∀ x y, ∃ e : O,
        raw b x.val y.val - A x y = algebraMap O K (π*e)

def CorrectBlocks {m : ℕ} (π : O) (raw : B → Bits m → Bits m → K) : Prop :=
  ∀ x y, ∃ e : O,
    algebraMap O K (matchingTarget O m x y) -
      (∑ b, raw b x y) = algebraMap O K (π*e)

/-- Collecting errors is lawful even when the individual values of
both families of summands are nonintegral. -/
theorem sum_congruence (π : O) (u : O) (raw replaced : B → K)
    (hU : ∃ e : O, algebraMap O K u-(∑ b, raw b)=algebraMap O K (π*e))
    (hReplace : ∀ b, ∃ e : O, raw b-replaced b=algebraMap O K (π*e)) :
    ∃ e : O, algebraMap O K u-(∑ b, replaced b)=algebraMap O K (π*e) := by
  obtain ⟨e,he⟩ := hU
  choose d hd using hReplace
  have htot := Finset.sum_congr rfl (fun b (_ : b∈Finset.univ) => hd b)
  rw [Finset.sum_sub_distrib] at htot
  refine ⟨e+∑ b, d b,?_⟩
  calc
    _ = (algebraMap O K u - ∑ b, raw b) + ((∑ b, raw b) - ∑ b, replaced b) := by ring
    _ = _ := by rw [he,htot,mul_add,map_add,Finset.mul_sum,map_sum]

theorem assemble_each {m : ℕ} (π : O) (cuts : B → Cut m)
    (raw : B → Bits m → Bits m → K) (H : B → ℕ) (caps : FiberCaps π cuts raw H) :
    ∃ M : B → Matrix (Bits m) (Bits m) K,
      (∀ b, (M b).rank≤2^(m-(cuts b).delta+(cuts b).hazard)*H b) ∧
      ∀ b x y, ∃ e : O, raw b x y - M b x y=algebraMap O K (π*e) := by
  unfold FiberCaps at caps
  choose A hA hAgree using caps
  let M (b : B) : Matrix (Bits m) (Bits m) K := assemble (cuts b) (A b)
  refine ⟨M,fun b => assemble_rank (cuts b) (A b) _ (hA b),fun b x y => ?_⟩
  change ∃ e : O, raw b x y - assemble (cuts b) (A b) x y=algebraMap O K (π*e)
  rw [assemble_on]
  exact hAgree b (fiberOf (cuts b) x y) ⟨x,rfl⟩ ⟨y,rfl⟩

/-- Changing proof-producing equality decisions preserves a determinant.
This avoids comparing two permutation enumerators by computation. -/
theorem det_index_decision {V R : Type*} [Fintype V] [CommRing R] (A : Matrix V V R)
    (d e : DecidableEq V) : (letI := d; A.det)=(letI := e; A.det) := by
  have h : d=e := by funext i j; exact Subsingleton.elim _ _
  subst e
  rfl

/-- Integer form of U7: multiply both sides by 2^m. This avoids
signed exponents and treats zeros and degenerate cuts uniformly. -/
theorem U7_scaled {m : ℕ} (π : O) (hz : IsLocalRing.residue O π=0)
    (cuts : B → Cut m) (raw : B → Bits m → Bits m → K) (H : B → ℕ)
    (correct : CorrectBlocks π raw) (caps : FiberCaps π cuts raw H) :
    2^m≤∑ b, min (2^m) (2^(m-(cuts b).delta+(cuts b).hazard)*H b) := by
  obtain ⟨M,hBound,hEach⟩ := assemble_each π cuts raw H caps
  have hSum (x y : Bits m) : ∃ e : O,
      algebraMap O K (matchingTarget O m x y) - (∑ b, M b x y)=algebraMap O K (π*e) :=
    sum_congruence π (matchingTarget O m x y) (fun b => raw b x y)
      (fun b => M b x y) (correct x y) (fun b => hEach b x y)
  let ro := (matchingTarget O m).map (IsLocalRing.residue O)
  have ht : ro.det≠0 := by
    change ((matchingTarget O m).map (IsLocalRing.residue O)).det≠0
    rw [matching_map]
    exact matching_det_ne_zero _ _
  have hFull : (letI := Classical.decEq (Bits m); ro.det≠0) := by
    have hd := det_index_decision ro (inferInstance : DecidableEq (Bits m))
      (Classical.decEq (Bits m))
    exact hd ▸ ht
  have hCard : Fintype.card (Bits m)=2^m := by simp [Bits]
  let bound (b : B) := 2^(m-(cuts b).delta+(cuts b).hazard)*H b
  calc
    2^m = Fintype.card (Bits m) := hCard.symm
    _ ≤ ∑ b, min (Fintype.card (Bits m)) (bound b) :=
      budget_of_square_blocks π hz (matchingTarget O m) M bound hFull hSum hBound
    _ = _ := Finset.sum_congr rfl (fun b _ => congrArg (fun a => min a (bound b)) hCard)

/-- Equation U7 in the paper's normalized form. The nonnegative
power ratio denotes the exact factor 2^(−δ+ell), then multiplies H. -/
theorem U7_normalized {m : ℕ} (π : O) (hz : IsLocalRing.residue O π=0)
    (cuts : B → Cut m) (raw : B → Bits m → Bits m → K) (H : B → ℕ)
    (correct : CorrectBlocks π raw) (caps : FiberCaps π cuts raw H) :
    (1:ℚ)≤∑ b, min 1 ((2:ℚ)^(m-(cuts b).delta+(cuts b).hazard)*H b/2^m) := by
  let N : ℚ := 2^m
  let weight (b : B) : ℚ := (2:ℚ)^(m-(cuts b).delta+(cuts b).hazard)*H b
  have hn : 0<N := pow_pos (by norm_num) _
  have hQ : N≤∑ b, min N (weight b) := by
    unfold N weight
    exact_mod_cast U7_scaled π hz cuts raw H correct caps
  have hc := (div_le_div_iff_of_pos_right hn).mpr hQ
  rw [div_self hn.ne',Finset.sum_div] at hc
  have hm (b : B) : min N (weight b)/N=min 1 (weight b/N) := by
    by_cases hh : weight b≤N
    · have hl : weight b/N≤1 := (div_le_iff₀ hn).mpr (by simpa using hh)
      rw [min_eq_right hh,min_eq_right hl]
    · have hh' : N≤weight b := le_of_not_ge hh
      have hl : 1≤weight b/N := (le_div_iff₀ hn).mpr (by simpa using hh')
      rw [min_eq_left hh',min_eq_left hl,div_self hn.ne']
  simp only [hm] at hc
  exact hc

#print axioms assemble_rank
#print axioms assemble_on
#print axioms sum_congruence
#print axioms assemble_each
#print axioms det_index_decision
#print axioms U7_scaled
#print axioms U7_normalized
end
end V8CapacityUnified.U7
