import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Finite endpoint-marking expectation (P9)

The sample space is a Cartesian product with one independently marked
slot for each equality. All weights, expectations, and conditioning
identities are finite sums of rational numbers.
-/

open scoped BigOperators

namespace GuardExpectation

section Product

variable {E A : Type*} [Fintype E] [DecidableEq E] [Fintype A]

/-- Product probability mass for an assignment. -/
def productMass (w : E → A → ℚ) (a : E → A) : ℚ := ∏ e, w e (a e)

/-- Finite rational product expectation. -/
def average (w : E → A → ℚ) (f : (E → A) → ℚ) : ℚ :=
  ∑ a, productMass w a * f a

theorem average_product (w f : E → A → ℚ) :
    average w (fun a => ∏ e, f e (a e)) = ∏ e, ∑ x, w e x * f e x := by
  simp only [average, productMass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun e x => w e x * f e x)).symm

theorem sum_productMass (w : E → A → ℚ) (hw : ∀ e, ∑ x, w e x = 1) :
    (∑ a, productMass w a) = 1 := by
  simpa only [average, Finset.prod_const_one, mul_one, hw]
    using average_product w (fun _ _ => 1)

theorem average_const (w : E → A → ℚ) (hw : ∀ e, ∑ x, w e x = 1) (c : ℚ) :
    average w (fun _ => c) = c := by
  rw [average, ← Finset.sum_mul, sum_productMass w hw, one_mul]

theorem average_sum {I : Type*} [Fintype I] (w : E → A → ℚ)
    (f : I → (E → A) → ℚ) :
    average w (fun a => ∑ i, f i a) = ∑ i, average w (f i) := by
  simp only [average, Finset.mul_sum]
  exact Finset.sum_comm

theorem average_add (w : E → A → ℚ) (f g : (E → A) → ℚ) :
    average w (fun a => f a + g a) = average w f + average w g := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_mulConst (w : E → A → ℚ) (f : (E → A) → ℚ) (c : ℚ) :
    average w (fun a => c * f a) = c * average w f := by
  simp only [average, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => by ring)

omit [DecidableEq E] [Fintype A] in
theorem productMass_nonneg (w : E → A → ℚ) (hw : ∀ e a, 0 ≤ w e a) (a : E → A) :
    0 ≤ productMass w a := by
  exact Finset.prod_nonneg (fun e _ => hw e (a e))

/-- A nonnegative normalized finite weight admits an outcome at or below
its average (without sampling or additional probability assumptions). -/
theorem exists_le_weighted_average {I : Type*} [Fintype I] (w f : I → ℚ)
    (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) :
    ∃ i : I, f i ≤ ∑ j, w j * f j := by
  classical
  have hne : (Finset.univ : Finset I).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at h1
    norm_num at h1
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ f hne
  refine ⟨i, ?_⟩
  have h := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hi j hj) (h0 j))
  rw [← Finset.sum_mul, h1, one_mul] at h
  exact h

theorem exists_sample_le_average (w : E → A → ℚ)
    (h0 : ∀ e a, 0 ≤ w e a) (h1 : ∀ e, ∑ a, w e a = 1) (f : (E → A) → ℚ) :
    ∃ a, f a ≤ average w f :=
  exists_le_weighted_average (productMass w) f (productMass_nonneg w h0) (sum_productMass w h1)

/-- A function of one coordinate, extended multiplicatively using identities. -/
def liftCoord (e : E) (f : A → ℚ) (j : E) (a : A) : ℚ :=
  if j = e then f a else 1

omit [Fintype A] in
theorem prod_liftCoord (e : E) (f : A → ℚ) (a : E → A) :
    (∏ j, liftCoord e f j (a j)) = f (a e) := by
  rw [Finset.prod_eq_single_of_mem e (Finset.mem_univ e)]
  · simp [liftCoord]
  · intro j _ hne
    simp [liftCoord, hne]

theorem average_coordinate (w : E → A → ℚ) (hw : ∀ j, ∑ a, w j a = 1)
    (e : E) (f : A → ℚ) :
    average w (fun a => f (a e)) = ∑ a, w e a * f a := by
  have h := average_product w (liftCoord e f)
  simp_rw [prod_liftCoord] at h
  rw [h, Finset.prod_eq_single_of_mem e (Finset.mem_univ e)]
  · simp [liftCoord]
  · intro j _ hne
    simp [liftCoord, hne, hw]

/-- Independence is proved directly from the Cartesian-product mass. -/
theorem average_pair (w : E → A → ℚ) (hw : ∀ j, ∑ a, w j a = 1)
    {e i : E} (hei : e ≠ i) (f g : A → ℚ) :
    average w (fun a => f (a e) * g (a i)) =
      (∑ a, w e a * f a) * (∑ a, w i a * g a) := by
  have h := average_product w (fun j a => liftCoord e f j a * liftCoord i g j a)
  simp_rw [Finset.prod_mul_distrib, prod_liftCoord] at h
  rw [h]
  have hf (j : E) : (∑ a, w j a * (liftCoord e f j a * liftCoord i g j a)) =
      (∑ a, w j a * liftCoord e f j a) * (∑ a, w j a * liftCoord i g j a) := by
    by_cases hje : j = e
    · subst j
      simp [liftCoord, hei, hw]
    · simp [liftCoord, hje, hw]
  simp_rw [hf, Finset.prod_mul_distrib]
  rw [← average_product w (liftCoord e f), ← average_product w (liftCoord i g)]
  simp_rw [prod_liftCoord, average_coordinate w hw]

end Product

section Moments

variable {A : Type*} [Fintype A] [DecidableEq A]

def indicator (s a : A) : ℚ := if a = s then 1 else 0

def centered (p : ℚ) (s a : A) : ℚ := indicator s a - p

theorem weighted_indicator (w : A → ℚ) (s : A) :
    (∑ a, w a * indicator s a) = w s := by
  rw [Finset.sum_eq_single_of_mem s (Finset.mem_univ s)]
  · simp [indicator]
  · intro a _ h
    simp [indicator, h]

theorem centered_mean (w : A → ℚ) (hw : ∑ a, w a = 1) (s : A) :
    (∑ a, w a * centered (w s) s a) = 0 := by
  simp only [centered, mul_sub, Finset.sum_sub_distrib, weighted_indicator, ← Finset.sum_mul, hw,
    one_mul, sub_self]

theorem centered_second (w : A → ℚ) (hw : ∑ a, w a = 1) (s : A) :
    (∑ a, w a * (centered (w s) s a)^2) = w s * (1-w s) := by
  have hpoint (a : A) :
      w a * (centered (w s) s a)^2 =
        (1-2*w s) * (w a * indicator s a) + w a * (w s)^2 := by
    by_cases h : a = s
    · simp [centered, indicator, h]; ring
    · simp [centered, indicator, h]
  rw [Finset.sum_congr rfl (fun a _ => hpoint a), Finset.sum_add_distrib, ← Finset.mul_sum,
    weighted_indicator, ← Finset.sum_mul, hw]
  ring

end Moments

section Variance

variable {E A : Type*} [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A]

/-- For two distinct equality vertices, the centered product has mean zero.
Two equalities sharing a physical cell remain different variables. -/
theorem centered_pair (w : E → A → ℚ) (hw : ∀ e, ∑ a, w e a = 1)
    (p : ℚ) (s : A) (hp : ∀ e, w e s = p) (e i : E) :
    average w (fun a => centered p s (a e) * centered p s (a i)) =
      if e = i then p*(1-p) else 0 := by
  by_cases h : e = i
  · subst i
    rw [if_pos rfl]
    simp only [← pow_two]
    rw [average_coordinate w hw e (fun x : A => (centered p s x)^2)]
    simpa only [hp e] using centered_second (w e) (hw e) s
  · rw [if_neg h, average_pair w hw h]
    rw [← hp e, centered_mean (w e) (hw e), zero_mul]

/-- Centered weighted load for a single sign and a single cell (or the
total count, by taking all weights equal to one). -/
def centeredLoad (p : ℚ) (s : A) (d : E → ℚ) (a : E → A) : ℚ :=
  ∑ e, d e * centered p s (a e)

omit [DecidableEq E] [Fintype A] in
theorem centeredLoad_eq (p : ℚ) (s : A) (d : E → ℚ) (a : E → A) :
    centeredLoad p s d a = (∑ e, d e * indicator s (a e)) - (∑ e, d e)*p := by
  simp only [centeredLoad, centered, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

/-- Exact variance of one weighted load, with no assumption on which
pairs of ports share a cell. The square of a repeated port multiplicity
appears on the diagonal. -/
theorem variance_centeredLoad (w : E → A → ℚ) (hw : ∀ e, ∑ a, w e a = 1)
    (p : ℚ) (s : A) (hp : ∀ e, w e s = p) (d : E → ℚ) :
    average w (fun a => (centeredLoad p s d a)^2) = (p*(1-p)) * ∑ e, (d e)^2 := by
  have hsq (a : E → A) :
      (centeredLoad p s d a)^2 =
        ∑ e, ∑ i, (d e * d i) * (centered p s (a e) * centered p s (a i)) := by
    rw [centeredLoad, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun i _ => by ring))
  simp_rw [hsq, average_sum, average_mulConst, centered_pair w hw p s hp]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
  · rw [if_pos rfl]
    ring
  · intro i _ hi
    rw [if_neg hi.symm, mul_zero]

end Variance

section P9

variable {E C : Type*} [Fintype E] [DecidableEq E] [Fintype C]

/-- The two signs are distinct distinguished values in a uniform L-way draw;
all other values are unmarked. -/
def signSymbol (L : ℕ) (hL : 2 ≤ L) (sign : Bool) : Fin L :=
  if sign then ⟨1, by omega⟩ else ⟨0, by omega⟩

theorem signSymbol_injective (L : ℕ) (hL : 2 ≤ L) :
    Function.Injective (signSymbol L hL) := by
  intro a b h
  cases a <;> cases b <;> simp_all [signSymbol, Fin.mk.injEq]

def uniform (E : Type*) (L : ℕ) : E → Fin L → ℚ := fun _ _ => (L:ℚ)⁻¹

omit [Fintype E] [DecidableEq E] in
theorem sum_uniform (L : ℕ) (hL : 0 < L) (e : E) :
    (∑ a, uniform E L e a) = 1 := by
  have hn : (L:ℚ) ≠ 0 := by positivity
  simp [uniform, nsmul_eq_mul]
  exact mul_inv_cancel₀ hn

/-- The two count deviations and all cell-load deviations in source P9.
Both ports of an equality in one cell use a single random mark and
one multiplicity-two weight. -/
def guardPotential {L : ℕ} (signSymbol : Bool → Fin L) (m : E → C → ℕ)
    (a : E → Fin L) : ℚ :=
  ∑ sign : Bool, ((centeredLoad (L:ℚ)⁻¹ (signSymbol sign) (fun _ => 1) a)^2 +
    ∑ c, (centeredLoad (L:ℚ)⁻¹ (signSymbol sign) (fun e => (m e c : ℚ)) a)^2)

theorem mean_guardPotential {L : ℕ} (hL : 0 < L) (sign : Bool → Fin L)
    (m : E → C → ℕ) :
    average (uniform E L) (guardPotential sign m) =
      2 * (L:ℚ)⁻¹ * (1-(L:ℚ)⁻¹) *
        ((Fintype.card E:ℚ) + ∑ c, ∑ e, (m e c:ℚ)^2) := by
  change average (uniform E L) (fun a =>
    ∑ b : Bool, ((centeredLoad (L:ℚ)⁻¹ (sign b) (fun _ => 1) a)^2 +
      ∑ c, (centeredLoad (L:ℚ)⁻¹ (sign b) (fun e => (m e c : ℚ)) a)^2)) = _
  simp only [average_sum, average_add]
  have h (b : Fin L) (d : E → ℚ) :
      average (uniform E L) (fun a => (centeredLoad (L:ℚ)⁻¹ b d a)^2) =
        (L:ℚ)⁻¹*(1-(L:ℚ)⁻¹)*∑ e, (d e)^2 :=
    variance_centeredLoad (uniform E L) (sum_uniform L hL) _ b (fun _ => rfl) d
  simp_rw [h]
  simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, Fintype.card_bool, Nat.cast_ofNat]
  ring

omit [DecidableEq E] in
theorem sq_multiplicity_sum_le (m : E → C → ℕ)
    (hMax : ∀ e c, m e c ≤ 2) (hPorts : ∀ e, ∑ c, m e c = 2) :
    (∑ c, ∑ e, (m e c:ℚ)^2) ≤ 4 * (Fintype.card E : ℚ) := by
  calc
    _ ≤ ∑ c, ∑ e, 2 * (m e c : ℚ) := by
      refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun e _ => ?_
      have h0 : 0 ≤ (m e c:ℚ) := by positivity
      have h2 : (m e c:ℚ) ≤ 2 := by exact_mod_cast hMax e c
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h2)]
    _ = _ := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ e : E, (4:ℚ) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          have h : (∑ c, (m e c:ℚ)) = 2 := by exact_mod_cast hPorts e
          rw [← Finset.mul_sum, h]
          norm_num
        _ = _ := by simp [nsmul_eq_mul, mul_comm]

/-- The exact constant 5 times M/L, for M equal to twice the number of
equalities. The proof permits coincident incidence cells. -/
theorem guardExpectation_le {L : ℕ} (hL : 0 < L) (sign : Bool → Fin L)
    (m : E → C → ℕ) (hMax : ∀ e c, m e c ≤ 2) (hPorts : ∀ e, ∑ c, m e c = 2) :
    average (uniform E L) (guardPotential sign m) ≤
      5 * (2 * (Fintype.card E : ℚ)) / (L : ℚ) := by
  rw [mean_guardPotential hL]
  let p : ℚ := (L:ℚ)⁻¹
  let n : ℚ := Fintype.card E
  have h1 : 1 ≤ (L:ℚ) := by exact_mod_cast hL
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    simpa only [inv_one] using (inv_le_inv₀ (by positivity : (0:ℚ) < L)
        (by norm_num : (0:ℚ) < 1)).mpr h1
  have hN : 0 ≤ n := by dsimp [n]; positivity
  have hfac : 0 ≤ 2 * p * (1-p) :=
    mul_nonneg (mul_nonneg (by norm_num) hp0) (sub_nonneg.mpr hp1)
  have hmult : (∑ c, ∑ e, (m e c:ℚ)^2) ≤ 4*n := sq_multiplicity_sum_le m hMax hPorts
  change 2*p*(1-p)*(n + ∑ c, ∑ e, (m e c:ℚ)^2) ≤ 5 * (2*n)/(L:ℚ)
  calc
    _ ≤ 2*p*(1-p)*(n+4*n) := mul_le_mul_of_nonneg_left (add_le_add_left hmult _) hfac
    _ ≤ 2*p*(n+4*n) := by
      have hfac' : 2*p*(1-p) ≤ 2*p := by
        have ht : 1-p ≤ 1 := by linarith
        simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (show 0 ≤ 2*p by positivity)
      exact mul_le_mul_of_nonneg_right hfac' (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, ← show (L:ℚ)⁻¹ = p from rfl]; ring

/-- There is one simultaneous endpoint marking for both signs and all cells. -/
theorem exists_good_marking {L : ℕ} (hL : 2 ≤ L)
    (m : E → C → ℕ) (hMax : ∀ e c, m e c ≤ 2) (hPorts : ∀ e, ∑ c, m e c = 2) :
    ∃ a : E → Fin L, guardPotential (signSymbol L hL) m a ≤
        5 * (2 * (Fintype.card E : ℚ)) / (L : ℚ) := by
  have hpos : 0 < L := by omega
  obtain ⟨a, ha⟩ := exists_sample_le_average (uniform E L)
    (fun _ _ => by unfold uniform; positivity) (sum_uniform L hpos)
    (guardPotential (signSymbol L hL) m)
  exact ⟨a, ha.trans (guardExpectation_le hpos _ m hMax hPorts)⟩

end P9

section Conditioning

variable {E A : Type*} [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A]

/-- Replace just the indicated marginal by the point mass at v. -/
def fixAt (w : E → A → ℚ) (e : E) (v : A) (i : E) (a : A) : ℚ :=
  if i=e then indicator v a else w i a

omit [Fintype E] [Fintype A] in
theorem fixAt_nonneg (w : E → A → ℚ) (h : ∀ e a, 0 ≤ w e a) (e : E) (v : A) :
    ∀ i a, 0 ≤ fixAt w e v i a := by
  intro i a
  unfold fixAt
  split
  · unfold indicator
    split <;> norm_num
  · exact h i a

omit [Fintype E] in
theorem fixAt_normalized (w : E → A → ℚ) (h : ∀ e, ∑ a, w e a = 1)
    (e : E) (v : A) :
    ∀ i, (∑ a, fixAt w e v i a) = 1 := by
  intro i
  by_cases hi : i=e
  · subst i
    simpa [fixAt] using weighted_indicator (fun _ : A => 1) v
  · simpa only [fixAt, if_neg hi] using h i

omit [Fintype A] in
theorem productMass_fixAt (w : E → A → ℚ) (e : E) (v : A) (a : E → A) :
    productMass (fixAt w e v) a = indicator v (a e) *
      ∏ i ∈ Finset.univ.erase e, w i (a i) := by
  rw [productMass, ← Finset.mul_prod_erase Finset.univ
    (fun i => fixAt w e v i (a i)) (Finset.mem_univ e)]
  have h : (∏ i ∈ Finset.univ.erase e, fixAt w e v i (a i)) =
      ∏ i ∈ Finset.univ.erase e, w i (a i) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    simp only [fixAt, if_neg (Finset.ne_of_mem_erase hi)]
  rw [h]
  simp [fixAt]

/-- Exact finite conditional expectation identity for any function.
It remains valid when some candidate marginal weights vanish. -/
theorem split_average_fixAt (w : E → A → ℚ) (f : (E → A) → ℚ) (e : E) :
    average w f = ∑ v, w e v * average (fixAt w e v) f := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single_of_mem (a e) (Finset.mem_univ (a e))]
  · rw [productMass_fixAt, productMass, ← Finset.mul_prod_erase Finset.univ
      (fun i => w i (a i)) (Finset.mem_univ e)]
    simp [indicator, mul_assoc]
  · intro v _ hv
    rw [productMass_fixAt]
    simp [indicator, hv.symm]

theorem exists_decreasing_fixAt (w : E → A → ℚ)
    (h0 : ∀ e a, 0 ≤ w e a) (h1 : ∀ e, ∑ a, w e a=1)
    (f : (E → A) → ℚ) (e : E) :
    ∃ v, average (fixAt w e v) f ≤ average w f := by
  rw [split_average_fixAt w f e]
  exact exists_le_weighted_average (w e) (fun v => average (fixAt w e v) f) (h0 e) (h1 e)

omit [Fintype E] [Fintype A] in
/-- Fix one Dirac marginal for each assignment coordinate in s. -/
def fixOn (w : E → A → ℚ) (s : Finset E) (a : E → A) (i : E) (v : A) : ℚ :=
  if i ∈ s then indicator (a i) v else w i v

omit [Fintype E] [Fintype A] in
theorem fixOn_insert (w : E → A → ℚ) {s : Finset E} {e : E}
    (he : e ∉ s) (v : A) (a : E → A) :
    fixOn (fixAt w e v) s a = fixOn w (insert e s) (Function.update a e v) := by
  funext i b
  by_cases hi : i = e
  · subst i
    simp [fixOn, fixAt, he]
  · simp [fixOn, fixAt, hi, Function.update_of_ne]

/-- Iterate the conditional method in the order encoded by the finite
induction. Each step is a local choice and keeps the earlier marginals
fixed. No scan of the whole product space is needed by the argument. -/
theorem exists_fixOn_le [Nonempty A] (s : Finset E) (w : E → A → ℚ)
    (h0 : ∀ e a, 0 ≤ w e a) (h1 : ∀ e, ∑ a, w e a=1)
    (f : (E → A) → ℚ) :
    ∃ a, average (fixOn w s a) f ≤ average w f := by
  induction s using Finset.induction_on generalizing w with
  | empty =>
    obtain ⟨v⟩ := (inferInstance : Nonempty A)
    have heq : fixOn w ∅ (fun _ => v) = w := by
      funext i a
      simp [fixOn]
    exact ⟨fun _ => v, by rw [heq]⟩
  | @insert e s he ih =>
    obtain ⟨v, hv⟩ := exists_decreasing_fixAt w h0 h1 f e
    obtain ⟨a, ha⟩ := ih (fixAt w e v) (fixAt_nonneg w h0 e v) (fixAt_normalized w h1 e v)
    rw [fixOn_insert w he] at ha
    exact ⟨Function.update a e v, ha.trans hv⟩

theorem average_fixOn_univ (w : E → A → ℚ) (f : (E → A) → ℚ) (a : E → A) :
    average (fixOn w Finset.univ a) f = f a := by
  rw [average, Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · simp [productMass, fixOn, indicator]
  · intro b _ hb
    have h : ∃ i, b i ≠ a i := by
      by_contra hh
      push_neg at hh
      exact hb (funext hh)
    obtain ⟨i, hi⟩ := h
    have h0 : productMass (fixOn w Finset.univ a) b = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [fixOn, indicator, hi])
    rw [h0, zero_mul]

/-- The same good-sample conclusion follows by conditional refinements
all the way to a single atom. -/
theorem exists_sample_by_conditioning [Nonempty A] (w : E → A → ℚ)
    (h0 : ∀ e a, 0 ≤ w e a) (h1 : ∀ e, ∑ a, w e a=1)
    (f : (E → A) → ℚ) :
    ∃ a, f a ≤ average w f := by
  obtain ⟨a, ha⟩ := exists_fixOn_le Finset.univ w h0 h1 f
  exact ⟨a, by rwa [average_fixOn_univ] at ha⟩

end Conditioning

section ConditionalMoments

variable {E A : Type*} [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A]

/-- Center each term using its own marginal, which can be a Dirac mass
for assigned variables or the original uniform weight for others. -/
def ownCenteredLoad (w : E → A → ℚ) (s : A) (d : E → ℚ) (a : E → A) : ℚ :=
  ∑ e, d e * centered (w e s) s (a e)

theorem ownCenteredLoad_mean (w : E → A → ℚ) (hw : ∀ e, ∑ a, w e a = 1)
    (s : A) (d : E → ℚ) :
    average w (ownCenteredLoad w s d) = 0 := by
  change average w (fun a => ∑ e, d e * centered (w e s) s (a e)) = 0
  rw [average_sum]
  simp_rw [average_mulConst]
  apply Finset.sum_eq_zero
  intro e _
  rw [average_coordinate w hw e (centered (w e s) s), centered_mean (w e) (hw e), mul_zero]

theorem ownCenteredLoad_second (w : E → A → ℚ) (hw : ∀ e, ∑ a, w e a = 1)
    (s : A) (d : E → ℚ) :
    average w (fun a => (ownCenteredLoad w s d a)^2) =
      ∑ e, (d e)^2 * (w e s * (1-w e s)) := by
  have hcov (e i : E) :
      average w (fun a => centered (w e s) s (a e)*centered (w i s) s (a i)) =
        if e=i then w e s * (1-w e s) else 0 := by
    by_cases h : e=i
    · subst i
      rw [if_pos rfl]
      simp only [← pow_two]
      rw [average_coordinate w hw e (fun a : A => (centered (w e s) s a)^2),
        centered_second (w e) (hw e)]
    · rw [if_neg h, average_pair w hw h, centered_mean (w e) (hw e), zero_mul]
  have hsq (a : E → A) :
      (ownCenteredLoad w s d a)^2 =
        ∑ e, ∑ i, (d e*d i) * (centered (w e s) s (a e)*centered (w i s) s (a i)) := by
    rw [ownCenteredLoad, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun i _ => by ring))
  simp_rw [hsq, average_sum, average_mulConst, hcov]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
  · rw [if_pos rfl]
    ring
  · intro i _ hi
    rw [if_neg hi.symm, mul_zero]

/-- A second moment relative to a fixed reference p: one sum for the
true variance and one square of a mean shift. This eliminates any product
space enumeration in computing conditional objective values. -/
def compressedSecond (w : E → A → ℚ) (p : ℚ) (s : A) (d : E → ℚ) : ℚ :=
  (∑ e, (d e)^2 * (w e s * (1-w e s))) + (∑ e, d e * (w e s-p))^2

theorem average_sq_eq_compressed (w : E → A → ℚ) (hw : ∀ e, ∑ a, w e a = 1)
    (p : ℚ) (s : A) (d : E → ℚ) :
    average w (fun a => (centeredLoad p s d a)^2) = compressedSecond w p s d := by
  let shift : ℚ := ∑ e, d e * (w e s-p)
  have hsplit (a : E → A) :
      centeredLoad p s d a = ownCenteredLoad w s d a + shift := by
    unfold centeredLoad ownCenteredLoad shift
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun e _ => by unfold centered; ring)
  have hsq (a : E → A) :
      (centeredLoad p s d a)^2 = (ownCenteredLoad w s d a)^2 +
        ((2*shift)*ownCenteredLoad w s d a + shift^2) := by
    rw [hsplit]
    ring
  simp_rw [hsq, average_add, average_mulConst]
  rw [ownCenteredLoad_second w hw, ownCenteredLoad_mean w hw,
    average_const w hw, mul_zero, zero_add]
  rfl

variable {C : Type*} [Fintype C]

/-- A sparse-size rational formula for the whole conditional P9 objective.
There are two signs. Each term on the right requires sums over E, not over
the independently marked assignments E → Fin L. -/
theorem conditional_guard_formula {L : ℕ} (w : E → Fin L → ℚ)
    (hw : ∀ e, ∑ a, w e a = 1) (sign : Bool → Fin L) (m : E → C → ℕ) :
    average w (guardPotential sign m) =
      ∑ b : Bool, (compressedSecond w (L:ℚ)⁻¹ (sign b) (fun _ => 1) +
        ∑ c, compressedSecond w (L:ℚ)⁻¹ (sign b) (fun e => (m e c : ℚ))) := by
  change average w (fun a => ∑ b : Bool,
    ((centeredLoad (L:ℚ)⁻¹ (sign b) (fun _ => 1) a)^2 +
      ∑ c, (centeredLoad (L:ℚ)⁻¹ (sign b) (fun e => (m e c : ℚ)) a)^2)) = _
  simp only [average_sum, average_add, average_sq_eq_compressed w hw]

end ConditionalMoments

section LiteralMarking

variable {E C : Type*} [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

/-- A literal labelled two-port equality. The labels may coincide. -/
def portMultiplicity (label : E → Bool → C) (e : E) (c : C) : ℕ :=
  ∑ port : Bool, if label e port = c then 1 else 0

omit [Fintype E] [DecidableEq E] [Fintype C] in
theorem portMultiplicity_le (label : E → Bool → C) (e : E) (c : C) :
    portMultiplicity label e c ≤ 2 := by
  unfold portMultiplicity
  calc
    _ ≤ ∑ _ : Bool, (1:ℕ) := by
      apply Finset.sum_le_sum
      intro b _
      split <;> norm_num
    _ = 2 := by simp

omit [Fintype E] [DecidableEq E] in
theorem sum_portMultiplicity (label : E → Bool → C) (e : E) :
    (∑ c, portMultiplicity label e c) = 2 := by
  unfold portMultiplicity
  rw [Finset.sum_comm]
  have h (b : Bool) : (∑ c, if label e b = c then (1:ℕ) else 0) = 1 := by
    rw [Finset.sum_eq_single_of_mem (label e b) (Finset.mem_univ _)]
    · simp
    · intro c _ hc
      simp [hc.symm]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, mul_one]
  rfl

/-- The source's two sets of marked equality vertices are disjoint by
construction. The marks are made per equality, not independently per port. -/
def markedSet {L : ℕ} (a : E → Fin L) (s : Fin L) : Finset E :=
  Finset.univ.filter (fun e => a e = s)

omit [DecidableEq E] [Fintype C] [DecidableEq C] in
theorem disjoint_markedSet {L : ℕ} (a : E → Fin L) {s t : Fin L} (hst : s ≠ t) :
    Disjoint (markedSet a s) (markedSet a t) := by
  refine Finset.disjoint_left.mpr (fun e hs ht => hst ?_)
  exact ((Finset.mem_filter.mp hs).2).symm.trans ((Finset.mem_filter.mp ht).2)

/-- P9's literal good marking obtained by conditional expectation, not
by an assumed independent sample. Both signs simultaneously obey the same
quadratic bound with M = 2 times the number of original equalities. -/
theorem exists_port_marking_by_conditioning {L : ℕ} (hL : 2 ≤ L) (label : E → Bool → C) :
    ∃ a : E → Fin L,
      Disjoint (markedSet a (signSymbol L hL false)) (markedSet a (signSymbol L hL true)) ∧
      guardPotential (signSymbol L hL) (portMultiplicity label) a ≤
        5 * (2 * (Fintype.card E : ℚ)) / (L:ℚ) := by
  have hpos : 0 < L := by omega
  letI : Nonempty (Fin L) := ⟨⟨0, hpos⟩⟩
  obtain ⟨a, ha⟩ := exists_sample_by_conditioning (uniform E L)
    (fun _ _ => by unfold uniform; positivity) (sum_uniform L hpos)
    (guardPotential (signSymbol L hL) (portMultiplicity label))
  refine ⟨a, disjoint_markedSet a (fun h => ?_), ha.trans (?_)⟩
  · exact Bool.noConfusion (signSymbol_injective L hL h)
  · exact guardExpectation_le hpos _ _ (portMultiplicity_le label) (sum_portMultiplicity label)

end LiteralMarking

#print axioms average_product
#print axioms average_pair
#print axioms variance_centeredLoad
#print axioms mean_guardPotential
#print axioms guardExpectation_le
#print axioms exists_good_marking
#print axioms split_average_fixAt
#print axioms exists_sample_by_conditioning
#print axioms average_sq_eq_compressed
#print axioms conditional_guard_formula
#print axioms exists_port_marking_by_conditioning

end GuardExpectation

