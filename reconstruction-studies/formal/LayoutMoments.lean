import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Reconstruction.LayoutMoments

open Finset
open scoped BigOperators Classical
noncomputable section

abbrev Bits (ι : Type*) := ι → Bool

/-- The sign convention makes the walk equal to h minus twice the number of true bits. -/
def sign (b : Bool) : ℝ := if b then -1 else 1

def walk {ι : Type*} [Fintype ι] (b : Bits ι) : ℝ := ∑ i, sign (b i)

def indicator (p : Prop) : ℝ := if p then 1 else 0

theorem expect_prod {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ) :
    (𝔼 x : ι × κ, f x.1 x.2) = 𝔼 i, 𝔼 j, f i j := by
  rw [← Finset.expect_product']
  simp

theorem expect_bool (f : Bool → ℝ) : (𝔼 b, f b) = (f false+f true)/2 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp [add_comm]

theorem expect_bits_succ (n : ℕ) (f : Bits (Fin (n+1)) → ℝ) :
    (𝔼 b, f b) =
      ((𝔼 b : Bits (Fin n), f (Fin.cons false b)) +
        (𝔼 b : Bits (Fin n), f (Fin.cons true b)))/2 := by
  calc
    _ = 𝔼 x : Bool × Bits (Fin n), f (Fin.cons x.1 x.2) :=
      Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm _ _
        (fun b => congrArg f ((Fin.consEquiv (fun _ : Fin (n+1) => Bool)).apply_symm_apply b).symm)
    _ = _ := by rw [expect_prod (fun (i : Bool) (b : Bits (Fin n)) => f (Fin.cons i b)), expect_bool]

theorem walk_cons (n : ℕ) (i : Bool) (b : Bits (Fin n)) :
    walk (Fin.cons i b) = sign i + walk b := by
  simp [walk, Fin.sum_univ_succ]

theorem walk_flip {ι : Type*} [Fintype ι] (b : Bits ι) :
    walk (fun i => !(b i)) = -walk b := by
  rw [walk, walk, ← sum_neg_distrib]
  exact sum_congr rfl fun i _ => by cases b i <;> norm_num [sign]

/-- Symmetry of the fair walk, for arbitrary real-valued test functions. -/
theorem expect_walk_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℝ → ℝ) :
    (𝔼 b : Bits ι, f (-(walk b))) = 𝔼 b : Bits ι, f (walk b) := by
  let flip : Bits ι ≃ Bits ι := Function.Involutive.toPerm
    (f := fun b i => !(b i)) (fun b => by funext i; simp)
  exact Fintype.expect_equiv flip _ _ (fun b => congrArg f (walk_flip b).symm)

/-- Reindex the fair walk without changing the law of any test function. -/
theorem expect_walk_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (f : ℝ → ℝ) :
    (𝔼 b : Bits ι, f (walk b)) = 𝔼 b : Bits κ, f (walk b) := by
  apply Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
  intro b
  apply congrArg f
  unfold walk
  exact Fintype.sum_equiv e _ _ (by simp)

/-- The exact second moment of a sum of independent fair signs. -/
theorem expect_walk_sq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (𝔼 b : Bits ι, walk b ^ 2) = (Fintype.card ι : ℝ) := by
  suffices step : ∀ n : ℕ, (𝔼 b : Bits (Fin n), walk b ^ 2) = (n : ℝ) from
    (expect_walk_equiv (Fintype.equivFin ι) (fun x => x^2)).trans (step (Fintype.card ι))
  intro n
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    rw [expect_bits_succ n (fun b => walk b^2)]
    simp only [walk_cons, sign, Bool.false_eq_true, if_false, if_true]
    rw [← expect_add_distrib, expect_div]
    have hf (b : Bits (Fin n)) : ((1+walk b)^2+(-1+walk b)^2)/2 = walk b^2+1 := by ring
    simp only [hf, expect_add_distrib, Fintype.expect_const, ih, Nat.cast_succ]

/-- The exact fourth moment, including the empty walk. -/
theorem expect_walk_fourth {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (𝔼 b : Bits ι, walk b ^ 4) = 3*(Fintype.card ι : ℝ)^2-2*Fintype.card ι := by
  suffices step : ∀ n : ℕ, (𝔼 b : Bits (Fin n), walk b ^ 4) = 3*(n:ℝ)^2-2*n from
    (expect_walk_equiv (Fintype.equivFin ι) (fun x => x^4)).trans (step (Fintype.card ι))
  intro n
  induction n with
  | zero => simp [walk]
  | succ n ih =>
    rw [expect_bits_succ n (fun b => walk b^4)]
    simp only [walk_cons, sign, Bool.false_eq_true, if_false, if_true]
    rw [← expect_add_distrib, expect_div]
    have hf (b : Bits (Fin n)) : ((1+walk b)^4+(-1+walk b)^4)/2 =
        walk b^4+6*walk b^2+1 := by ring
    simp only [hf, expect_add_distrib, ← mul_expect, Fintype.expect_const, ih, expect_walk_sq,
      Fintype.card_fin, Nat.cast_succ]
    ring

/-- The two-sided fourth-moment probability estimate used in Corollaries 2 and 5. -/
theorem walk_square_tail {ι : Type*} [Fintype ι] [DecidableEq ι] (hn : 0 < Fintype.card ι) :
    (1:ℝ)/12 ≤ 𝔼 b : Bits ι, indicator ((Fintype.card ι : ℝ)/2 ≤ walk b^2) := by
  let n : ℝ := Fintype.card ι
  have hn0 : 0 < n := by dsimp [n]; exact_mod_cast hn
  let f (b : Bits ι) := walk b^2
  let g (b : Bits ι) := indicator (n/2 ≤ f b)
  have hm2 : (𝔼 b, f b) = n := expect_walk_sq
  have hm4 : (𝔼 b, f b^2) ≤ 3*n^2 := by
    simp only [f, ← pow_mul, show (2:ℕ)*2=4 by decide, expect_walk_fourth, n]
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
    linarith
  have hg (b : Bits ι) : g b ^ 2 = g b := by
    dsimp [g, indicator]
    split_ifs <;> norm_num
  have hP : 0 ≤ 𝔼 b, g b := expect_nonneg (fun b _ => by
    dsimp [g, indicator]
    split_ifs <;> norm_num)
  have htrunc : n/2 ≤ 𝔼 b, f b*g b := by
    have hstep (b : Bits ι) : f b ≤ f b*g b+n/2 := by
      dsimp [g, indicator]
      split_ifs with he
      · simp only [mul_one]
        linarith
      · simp only [mul_zero, zero_add]
        exact (lt_of_not_ge he).le
    have ht := expect_le_expect (fun b (_ : b ∈ (univ : Finset (Bits ι))) => hstep b)
    rw [expect_add_distrib, Fintype.expect_const, hm2] at ht
    linarith
  have hc := expect_mul_sq_le_sq_mul_sq (univ : Finset (Bits ι)) f g
  simp_rw [hg] at hc
  have hs := pow_le_pow_left₀ (show 0 ≤ n/2 by positivity) htrunc 2
  have h4 := mul_le_mul_of_nonneg_right hm4 hP
  have hall := hs.trans (hc.trans h4)
  change (1:ℝ)/12 ≤ 𝔼 b, g b
  apply le_of_mul_le_mul_left ?_ (show 0 < 3*n^2 by positivity)
  calc
    _ = (n/2)^2 := by ring
    _ ≤ _ := hall

theorem sqrt_le_abs_iff {a x : ℝ} (ha : 0 ≤ a) :
    Real.sqrt a ≤ |x| ↔ a ≤ x^2 := by
  rw [← sq_le_sq₀ (Real.sqrt_nonneg a) (abs_nonneg x)] at *
  rw [Real.sq_sqrt ha, sq_abs]

/-- One-sided probability at the paper's square-root threshold. -/
theorem walk_positive_tail {ι : Type*} [Fintype ι] [DecidableEq ι] (hn : 0 < Fintype.card ι) :
    (1:ℝ)/24 ≤ 𝔼 b : Bits ι, indicator (Real.sqrt ((Fintype.card ι : ℝ)/2) ≤ walk b) := by
  let a := (Fintype.card ι : ℝ)/2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hstep (b : Bits ι) : indicator (a ≤ walk b^2) ≤
      indicator (Real.sqrt a ≤ walk b) + indicator (Real.sqrt a ≤ -walk b) := by
    simp only [indicator, ← sqrt_le_abs_iff ha, le_abs]
    by_cases hx : Real.sqrt a ≤ walk b <;> by_cases hy : Real.sqrt a ≤ -walk b <;> simp [hx,hy]
  have hh := expect_le_expect (fun b (_ : b ∈ (univ : Finset (Bits ι))) => hstep b)
  rw [expect_add_distrib, expect_walk_neg (fun x => indicator (Real.sqrt a ≤ x))] at hh
  have hx := walk_square_tail (ι := ι) hn
  change (1:ℝ)/12 ≤ 𝔼 b : Bits ι, indicator (a ≤ walk b^2) at hx
  linarith

/-- First absolute moment at the constant used in Corollary 2. -/
theorem expect_abs_walk {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Real.sqrt ((Fintype.card ι : ℝ)/2)/12 ≤ 𝔼 b : Bits ι, |walk b| := by
  by_cases hn : 0 < Fintype.card ι
  · let a := (Fintype.card ι : ℝ)/2
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hstep (b : Bits ι) : Real.sqrt a * indicator (a ≤ walk b^2) ≤ |walk b| := by
      unfold indicator
      split_ifs with he
      · simpa only [mul_one] using (sqrt_le_abs_iff ha).mpr he
      · simp
    have hw := expect_le_expect (fun b (_ : b ∈ (univ : Finset (Bits ι))) => hstep b)
    rw [← mul_expect] at hw
    simpa only [mul_one_div] using (mul_le_mul_of_nonneg_left (walk_square_tail hn) (Real.sqrt_nonneg a)).trans hw
  · have hzero : Fintype.card ι = 0 := by omega
    simp only [hzero, Nat.cast_zero, zero_div, Real.sqrt_zero]
    exact expect_nonneg (fun b _ => abs_nonneg _)

/-- A deterministic bias cannot decrease the expected absolute value of the fair walk. -/
theorem expect_abs_walk_le_shift {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ℝ) :
    (𝔼 b : Bits ι, |walk b|) ≤ 𝔼 b : Bits ι, |z + walk b| := by
  have hstep (b : Bits ι) : 2*|walk b| ≤ |z+walk b|+|z + -walk b| := by
    have h := abs_add_le (z+walk b) (-(z + -walk b))
    rw [abs_neg, show z+walk b + -(z + -walk b) = 2*walk b by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
    exact h
  have hw := expect_le_expect (fun b (_ : b ∈ (univ : Finset (Bits ι))) => hstep b)
  rw [← mul_expect, expect_add_distrib, expect_walk_neg (fun x => |z+x|)] at hw
  linarith

/-- The lower expected positive excess used in Corollary 5, before multiplying by two. -/
theorem expect_walk_excess {ι : Type*} [Fintype ι] [DecidableEq ι] (R : ℕ)
    (hh : (8:ℝ)*(R+1)^2 ≤ Fintype.card ι) :
    Real.sqrt ((Fintype.card ι : ℝ)/2)/48 ≤
      𝔼 b : Bits ι, max 0 (walk b-R) := by
  let a := Real.sqrt ((Fintype.card ι : ℝ)/2)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha : 2*((R:ℝ)+1) ≤ a := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    nlinarith only [hh]
  have hn : 0 < Fintype.card ι := by
    have hpos : 0 < (Fintype.card ι : ℝ) := lt_of_lt_of_le (by positivity) hh
    exact_mod_cast hpos
  have hstep (b : Bits ι) : (a/2)*indicator (a ≤ walk b) ≤ max 0 (walk b-R) := by
    unfold indicator
    split_ifs with he
    · rw [mul_one]
      exact (show a/2 ≤ walk b-R by linarith only [ha, he]).trans (le_max_right _ _)
    · simp
  have hw := expect_le_expect (fun b (_ : b ∈ (univ : Finset (Bits ι))) => hstep b)
  rw [← mul_expect] at hw
  have htail := mul_le_mul_of_nonneg_left (walk_positive_tail hn) (show 0 ≤ a/2 by positivity)
  change a/48 ≤ _
  calc
    _ = a/2*(1/24) := by ring
    _ ≤ _ := htail.trans hw

end
end Reconstruction.LayoutMoments
