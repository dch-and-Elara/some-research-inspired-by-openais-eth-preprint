import P5MainIteratorWeights
import P5MainIteratorTailPoint
import Mathlib.Data.Nat.Sqrt

/-! Uniform fair-binomial escape from every omitted set of R weights.
The usual central interval is only one special case. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real

noncomputable def tailConstant : ℝ := exp (-16)/8

theorem tailConstant_pos : 0<tailConstant := by unfold tailConstant; positivity

theorem central_window_sqrt (n : ℕ) (hn : 64≤n) :
    8*Nat.sqrt n≤n ∧ sqrt (n:ℝ)≤2*(Nat.sqrt n:ℝ) := by
  let w := Nat.sqrt n
  have h₀ : 8≤w := Nat.le_sqrt'.mpr (by norm_num; omega)
  have h₁ : w*w≤n := Nat.sqrt_le n
  have h₂ : n<(w+1)*(w+1) := Nat.lt_succ_sqrt n
  have h₃ : w+1≤2*w := by omega
  have hw := Nat.mul_le_mul h₃ h₃
  have hbound : (n:ℝ)≤(2*(w:ℝ))^2 := by exact_mod_cast (show n≤(2*w)^2 by rw [pow_two]; omega)
  refine ⟨?_,(sqrt_le_iff).mpr ⟨by positivity,hbound⟩⟩
  exact (Nat.mul_le_mul_right w h₀).trans h₁

theorem fair_binomial_uniform_tail (Q n R : ℕ) (omitted : Finset ℕ)
    (hn : 64≤n) (hQ : n≤Q) (hQ4N : Q≤4*n) (hR : 16*R≤Q)
    (hs : omitted.card≤R) :
    tailConstant * exp (-(64*(R:ℝ)^2/(Q:ℝ))) ≤
      binomialMass n (fun j => j∉omitted) := by
  let w := Nat.sqrt n
  let l := n/2
  let W := Finset.Ico l (l+R+w)
  let S := W \ omitted
  have hw := central_window_sqrt n hn
  have h₀ : 8*w≤n := hw.1
  have hR' : 4*R≤n := by omega
  have hcard : W.card=R+w := by
    dsimp [W]; rw [Nat.card_Ico]; omega
  have hS : w≤S.card := by
    have h := Finset.le_card_sdiff omitted W
    dsimp [S]; omega
  have hsqrt : 0<sqrt (n:ℝ) := sqrt_pos.2 (by exact_mod_cast (by omega : 0<n))
  have hQ' : 0<(Q:ℝ) := by exact_mod_cast (by omega : 0<Q)
  have hn' : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hwsq : (w:ℝ)^2≤(n:ℝ) := by exact_mod_cast Nat.sqrt_le' n
  have hq4 : (Q:ℝ)≤4*(n:ℝ) := by exact_mod_cast hQ4N
  let p := (1/(4*sqrt (n:ℝ))) * exp (-(64*(R:ℝ)^2/(Q:ℝ)+16))
  have hp : 0≤p := by dsimp [p]; positivity
  have hmain (j : ℕ) (hj : j∈S) : p ≤ fairPoint n j := by
    have hjW := (Finset.mem_sdiff.mp hj).1
    have hlo := (Finset.mem_Ico.mp hjW).1
    have hhi := (Finset.mem_Ico.mp hjW).2
    let d := j-l
    have hjd : j = l+d := by dsimp [d]; omega
    have hdb : d≤R+w := by dsimp [d]; omega
    have hsquare : (d:ℝ)^2≤2*(R:ℝ)^2+2*(n:ℝ) := by
      have hdb' : (d:ℝ)≤(R:ℝ)+(w:ℝ) := by exact_mod_cast hdb
      have H := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(d:ℝ)) hdb' 2
      nlinarith only [H,hwsq,sq_nonneg ((R:ℝ)-(w:ℝ))]
    have hs' : (d:ℝ)^2*8 ≤ 16*(R:ℝ)^2+16*(n:ℝ) := by linarith only [hsquare]
    have hratio : (8/(n:ℝ))*(d:ℝ)^2 ≤ 64*(R:ℝ)^2/(Q:ℝ)+16 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hn').mpr
      have aux :
          16*(R:ℝ)^2 ≤ (64*(R:ℝ)^2/(Q:ℝ))*(n:ℝ) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hQ').mpr
        calc
          _ ≤ 16*(R:ℝ)^2*(4*(n:ℝ)) :=
            mul_le_mul_of_nonneg_left hq4 (by positivity)
          _ = _ := by ring
      linarith only [hs',aux]
    rw [hjd]
    have h8 : 8*(n/2+d)≤7*n := by dsimp [l] at hjd hhi; omega
    have he := exp_le_exp.mpr (neg_le_neg hratio)
    exact (mul_le_mul_of_nonneg_left (by simpa only [neg_mul] using he) (by positivity)).trans
      (fair_binomial_point_lower n d (by omega) h8)
  have hle : S⊆(Finset.range (n+1)).filter (fun j => j∉omitted) := by
    intro j hj
    have ht := Finset.mem_sdiff.mp hj
    have hhi := (Finset.mem_Ico.mp ht.1).2
    apply Finset.mem_filter.mpr
    dsimp [l] at hhi
    exact ⟨Finset.mem_range.mpr (by omega),ht.2⟩
  have hwp : (w:ℝ)*p ≤ (S.card:ℝ)*p :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hp
  calc
    _ = (sqrt (n:ℝ)/2)*p := by
      unfold tailConstant p
      rw [show -(64*(R:ℝ)^2/(Q:ℝ)+16)= -16 + -(64*(R:ℝ)^2/(Q:ℝ)) by ring, exp_add]
      field_simp
      norm_num
    _ ≤ (w:ℝ)*p := mul_le_mul_of_nonneg_right (by dsimp [w]; linarith only [hw.2]) hp
    _ ≤ (S.card:ℝ)*p := hwp
    _ = ∑ _j∈S,p := by simp
    _ ≤ ∑ j∈S,fairPoint n j := Finset.sum_le_sum hmain
    _ ≤ ∑ j∈(Finset.range (n+1)).filter (fun j => j∉omitted),fairPoint n j :=
      Finset.sum_le_sum_of_subset_of_nonneg hle (fun j _ _ => fairPoint_nonneg _ _)
    _ = _ := by
      unfold binomialMass fairPoint
      rw [Nat.cast_sum,Finset.sum_div]
      exact Finset.sum_congr (by ext j; simp) (fun _ _ => rfl)

#print axioms tailConstant_pos
#print axioms central_window_sqrt
#print axioms fair_binomial_uniform_tail
end P5MainIterator
