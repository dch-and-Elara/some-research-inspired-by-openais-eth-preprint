import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Numerical normalization of the X1 union bound and integer margins.
The strict budget also ensures each requested margin is large enough
that rounding the lower bound up loses no factor beyond 2. -/
namespace Paper5.HybridMulti
open scoped BigOperators Classical
open Real

variable {S : Type*} [Fintype S]

theorem normalized_budget_and_ceils (n : ℕ) (hn : 0<n) (k : S→ℕ)
    (hk : ∀ s,0<k s) (K H : ℝ) (hK : 0<K) (hH : 0<H)
    (w m : S→ℝ) (hw : ∀ s,0<w s)
    (hm : ∀ s,K*(n:ℝ)*w s/(6*H)≤m s)
    (hBudget : (36*7776/K^2)*(H^2/(n:ℝ))*(∑ s,(k s:ℝ)/(w s)^2)<1) :
    (∑ s,(k s:ℝ)*(7776*(n:ℝ))/(m s)^2)<1 ∧
      ∀ s, (⌈K*(n:ℝ)*w s/(12*H)⌉₊:ℝ)≤m s := by
  have hN : 0<(n:ℝ) := by exact_mod_cast hn
  have hm0 (s : S) : 0<K*(n:ℝ)*w s/(6*H) :=
    div_pos (mul_pos (mul_pos hK hN) (hw s)) (mul_pos (by norm_num) hH)
  have hPos (s : S) : 0<m s := (hm0 s).trans_le (hm s)
  have hTerm (s : S) : (k s:ℝ)*(7776*(n:ℝ))/(m s)^2≤
      ((36*7776/K^2)*(H^2/(n:ℝ)))*((k s:ℝ)/(w s)^2) := by
    calc
      _ ≤ (k s:ℝ)*(7776*(n:ℝ))/(K*(n:ℝ)*w s/(6*H))^2 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos (hm0 s) 2)
          (pow_le_pow_left₀ (hm0 s).le (hm s) _)
      _ = _ := by
        have hs := hw s
        field_simp
        ring
  have hSum := Finset.sum_le_sum (fun s (_hs : s∈(Finset.univ : Finset S))=>hTerm s)
  rw [←Finset.mul_sum] at hSum
  have hs : (∑ s,(k s:ℝ)*(7776*(n:ℝ))/(m s)^2)<1 := hSum.trans_lt hBudget
  refine ⟨hs,fun s=>?_⟩
  have h1 : (k s:ℝ)*(7776*(n:ℝ))/(m s)^2<1 :=
    (Finset.single_le_sum (fun a (_ha : a∈(Finset.univ : Finset S))=>
      (show 0≤(k a:ℝ)*(7776*(n:ℝ))/(m a)^2 by positivity))
      (Finset.mem_univ s)).trans_lt hs
  have h2 : (k s:ℝ)*(7776*(n:ℝ))<(m s)^2 := by
    simpa only [one_mul] using (div_lt_iff₀ (pow_pos (hPos s) 2)).mp h1
  have hN1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hk1 : (1:ℝ)≤k s := by exact_mod_cast hk s
  have h3 : (7776:ℝ)≤(k s:ℝ)*(7776*(n:ℝ)) := by
    have he : (7776:ℝ)≤7776*(n:ℝ) := by linarith only [hN1]
    calc
      _ ≤ 1*(7776*(n:ℝ)) := by simpa only [one_mul] using he
      _ ≤ _ := mul_le_mul_of_nonneg_right hk1 (by positivity)
  have hm2 : (2:ℝ)≤m s := by
    by_contra! ht
    have hp := pow_le_pow_left₀ (hPos s).le ht.le 2
    norm_num at hp
    linarith only [h2,h3,hp]
  let L := K*(n:ℝ)*w s/(12*H)
  have hL : 0≤L := (div_pos (mul_pos (mul_pos hK hN) (hw s)) (mul_pos (by norm_num) hH)).le
  have hLL : 2*L≤m s := by
    have he : 2*L=K*(n:ℝ)*w s/(6*H) := by unfold L; ring
    rw [he]
    exact hm s
  exact (Nat.ceil_lt_add_one hL).le.trans (by linarith only [hLL,hm2])

#print axioms normalized_budget_and_ceils
end Paper5.HybridMulti
