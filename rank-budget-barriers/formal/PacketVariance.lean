import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-! Finite product bounded differences for P11. The proof is entirely
over rationals; no measurable conditional expectations or oracle costs. -/

namespace PacketVariance
open scoped BigOperators
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B]

def avg (w f : A → ℚ) : ℚ := ∑ a, w a * f a
def variance (w f : A → ℚ) : ℚ := avg w (fun a => (f a - avg w f)^2)
def prob (w : A → ℚ) : Prop := (∀ a, 0 ≤ w a) ∧ (∑ a, w a) = 1

theorem avg_le (w f g : A → ℚ) (hp : prob w) (h : ∀ a, f a ≤ g a) :
    avg w f ≤ avg w g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hp.1 a)

theorem avg_const (w : A → ℚ) (hp : prob w) (c : ℚ) :
    avg w (fun _ => c) = c := by
  unfold avg
  rw [← Finset.sum_mul, hp.2, one_mul]

theorem avg_add (w f g : A → ℚ) :
    avg w (fun a => f a+g a) = avg w f + avg w g := by
  simp [avg, mul_add, Finset.sum_add_distrib]

theorem avg_sub (w f g : A → ℚ) :
    avg w (fun a => f a-g a) = avg w f - avg w g := by
  simp [avg, mul_sub, Finset.sum_sub_distrib]

theorem avg_mul (w f : A → ℚ) (c : ℚ) :
    avg w (fun a => f a*c) = avg w f * c := by
  simp only [avg, ← mul_assoc, Finset.sum_mul]

theorem variance_center (w f : A → ℚ) (p : prob w) (c : ℚ) :
    avg w (fun a => (f a-c)^2) = variance w f + (avg w f-c)^2 := by
  let m := avg w f
  have hz : avg w (fun a => f a-m) = 0 := by rw [avg_sub, avg_const w p]; exact sub_self m
  have h (a : A) : (f a-c)^2 = ((f a-m)^2+(f a-m)*(2*(m-c)))+(m-c)^2 := by ring
  simp_rw [h]
  rw [avg_add, avg_add, avg_mul, hz, zero_mul, add_zero, avg_const w p]
  rfl

def prodWeight (w : A → ℚ) (v : B → ℚ) (x : A × B) : ℚ := w x.1 * v x.2

theorem avg_product (w : A → ℚ) (v : B → ℚ) (f : A × B → ℚ) :
    avg (prodWeight w v) f = avg w (fun a => avg v (fun b => f (a,b))) := by
  simp [avg, prodWeight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem prob_product (w : A → ℚ) (v : B → ℚ) (hw : prob w) (hv : prob v) :
    prob (prodWeight w v) := by
  refine ⟨fun a => mul_nonneg (hw.1 a.1) (hv.1 a.2), ?_⟩
  simp [prodWeight, Fintype.sum_prod_type, ← Finset.mul_sum, hw.2, hv.2]

theorem variance_product (w : A → ℚ) (v : B → ℚ) (f : A × B → ℚ) (hv : prob v) :
    variance (prodWeight w v) f =
      avg w (fun a => variance v (fun b => f (a,b))) +
      variance w (fun a => avg v (fun b => f (a,b))) := by
  conv_lhs => rw [variance, avg_product, avg_product]
  simp_rw [variance_center v _ hv]
  rw [avg_add, variance]

/-- Replacing the whole first type can change the result by at most c,
while the remaining product already has variance at most K. -/
theorem append_bound [Nonempty A] (w : A → ℚ) (v : B → ℚ) (f : A × B → ℚ)
    (hw : prob w) (hv : prob v) (c K : ℚ)
    (diff : ∀ a a' b, |f (a,b) - f (a',b)| ≤ c)
    (htail : ∀ a, variance v (fun b => f (a,b)) ≤ K) :
    variance (prodWeight w v) f ≤ c^2+K := by
  let m := fun a => avg v (fun b => f (a,b))
  let a₀ : A := Classical.choice inferInstance
  have hm (a : A) : |m a-m a₀| ≤ c := by
    rw [abs_le]
    have h₁ : avg v (fun _ => -c) ≤ avg v (fun b => f (a,b)-f (a₀,b)) :=
      avg_le _ _ _ hv (fun b => (abs_le.mp (diff a a₀ b)).1)
    have h₂ : avg v (fun b => f (a,b)-f (a₀,b)) ≤ avg v (fun _ => c) :=
      avg_le _ _ _ hv (fun b => (abs_le.mp (diff a a₀ b)).2)
    rw [avg_const _ hv, avg_sub] at h₁
    rw [avg_const _ hv, avg_sub] at h₂
    exact ⟨h₁,h₂⟩
  have houter : variance w m ≤ c^2 := by
    have h₂ := avg_le w (fun a => (m a-m a₀)^2) (fun _ => c^2) hw
      (fun a => by
        have h' := pow_le_pow_left₀ (abs_nonneg _) (hm a) 2
        simpa only [sq_abs] using h')
    rw [variance_center _ _ hw, avg_const _ hw] at h₂
    nlinarith [sq_nonneg (avg w m - m a₀)]
  have ht : avg w (fun a => variance v (fun b => f (a,b))) ≤ K := by
    have h := avg_le _ _ _ hw htail
    rwa [avg_const _ hw] at h
  rw [variance_product w v f hv]
  exact (add_le_add ht houter).trans_eq (add_comm _ _)

theorem avg_equiv {C : Type*} [Fintype C] (e : A ≃ C) (w f : C → ℚ) :
    avg (w ∘ e) (f ∘ e) = avg w f := by
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem variance_equiv {C : Type*} [Fintype C] (e : A ≃ C) (w f : C → ℚ) :
    variance (w ∘ e) (f ∘ e) = variance w f := by
  rw [variance, avg_equiv]
  change avg (w ∘ e) ((fun x => (f x-avg w f)^2) ∘ e) = _
  exact avg_equiv e w _

variable {n : ℕ}

def product {T : Fin n → Type*} (w : ∀ i, T i → ℚ) (a : ∀ i, T i) : ℚ :=
  ∏ i, w i (a i)

/-- Functions differing only at coordinate i have outcomes at distance at
most c i. Different types may have different finite spaces and laws. -/
def sensitive {T : Fin n → Type*} (f : (∀ i, T i) → ℚ) (c : Fin n → ℚ) : Prop :=
  ∀ i a b, (∀ j, j ≠ i → a j = b j) → |f a-f b| ≤ c i

theorem bounded_differences {T : Fin n → Type*} [∀ i, Fintype (T i)]
    [∀ i, Nonempty (T i)] (w : ∀ i, T i → ℚ) (f : (∀ i, T i) → ℚ)
    (c : Fin n → ℚ) (hw : ∀ i, prob (w i))
    (hd : sensitive f c) :
    variance (product w) f ≤ ∑ i, (c i)^2 := by
  classical
  induction n with
  | zero =>
    have he (a b : (i : Fin 0) → T i) : a = b := by funext i; exact Fin.elim0 i
    let a₀ : (i : Fin 0) → T i := fun i => Fin.elim0 i
    have hf : f = fun _ => f a₀ := by funext a; rw [he a a₀]
    have hp : prob (product w) := by simp [prob, product]
    rw [hf, variance, avg_const _ hp, avg_const _ hp]
    simp
  | succ n ih =>
    let E : T 0 × ((i : Fin n) → T i.succ) ≃ ((i : Fin (n+1)) → T i) :=
      (Fin.consEquiv T)
    let v := product (fun i => w i.succ)
    have hv : prob v := by
      refine ⟨fun t => Finset.prod_nonneg (fun i _ => (hw i.succ).1 (t i)), ?_⟩
      unfold v product
      rw [← Fintype.prod_sum]
      exact Finset.prod_eq_one fun i _ => (hw i.succ).2
    have hp : product w ∘ E = prodWeight (w 0) v := by
      funext x
      rcases x with ⟨a,b⟩
      simp [E, product, v, prodWeight, Fin.prod_univ_succ]
    let F := f ∘ E
    rw [← variance_equiv E, hp]
    rw [Fin.sum_univ_succ]
    apply append_bound (w 0) v F (hw 0) hv _ _
    · intro a a' b
      apply hd 0
      intro j hj
      cases j using Fin.cases with
      | zero => exact False.elim (hj rfl)
      | succ j => simp [E]
    · intro a
      apply ih (T := fun i => T i.succ) (w := fun i => w i.succ)
        (f := fun b => F (a,b)) (c := fun i => c i.succ) (fun i => hw i.succ)
      intro i x y hxy
      apply hd i.succ
      intro j hj
      cases j using Fin.cases with
      | zero => simp [E]
      | succ j => simpa [E] using hxy j (fun h => hj (congrArg Fin.succ h))

#print axioms variance_center
#print axioms variance_product
#print axioms append_bound
#print axioms bounded_differences
end
end PacketVariance