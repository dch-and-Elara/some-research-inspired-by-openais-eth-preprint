import S7Arithmetic

/-! Weighted ordered-pair counting in a dyadic shell. -/
namespace S7
open Finset
open scoped BigOperators
noncomputable section

abbrev Shell (n : ℕ) := Fin (2^n)

def residue {n : ℕ} (s : Fin n) (x : Shell n) : Fin (2^s.val) :=
  ⟨x.val % 2^s.val, Nat.mod_lt _ (by positivity)⟩

def classWeight {n : ℕ} (q : Shell n → ℚ) (s : Fin n) (c : Fin (2^s.val)) : ℚ :=
  ∑ x ∈ univ with residue s x = c, q x

def shellInteraction {n : ℕ} (q : Shell n → ℚ) (t : Shell n) : ℚ :=
  ∑ s : Fin n, ∑ x ∈ univ with residue s x = residue s t ∧ x ≠ t, q x

theorem classWeight_total {n : ℕ} (q : Shell n → ℚ) (s : Fin n) :
    (∑ c, classWeight q s c) = ∑ x, q x :=
  sum_fiberwise _ _ _

theorem classWeight_cauchy {n : ℕ} (q : Shell n → ℚ) (s : Fin n) :
    (∑ t, q t)^2 / 2^s.val ≤ ∑ c, classWeight q s c ^ 2 := by
  apply (div_le_iff₀ (by positivity)).2
  have hs := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin (2^s.val)))
    (classWeight q s) (fun _ => (1:ℚ))
  simp [classWeight_total] at hs
  simpa [mul_comm] using hs

theorem shellInteraction_eq {n : ℕ} (q : Shell n → ℚ) :
    (∑ t, q t * shellInteraction q t) =
      ∑ s : Fin n, ((∑ c, classWeight q s c ^ 2) - ∑ t, q t ^ 2) := by
  simp only [shellInteraction, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  have hfilter (t : Shell n) :
      (∑ x ∈ univ with residue s x = residue s t ∧ x ≠ t, q x) =
        classWeight q s (residue s t) - q t := by
    have he : (univ.filter fun x => residue s x = residue s t ∧ x ≠ t) =
        (univ.filter fun x => residue s x = residue s t).erase t := by
      ext x
      simp [and_comm]
    rw [he, classWeight]
    exact eq_sub_of_add_eq (sum_erase_add _ _ (mem_filter.mpr ⟨mem_univ _,rfl⟩))
  simp only [← mul_sum, hfilter, mul_sub, sum_sub_distrib, ← pow_two]
  congr 1
  rw [← sum_fiberwise univ (residue s)]
  apply sum_congr rfl
  intro c _
  rw [classWeight, pow_two, sum_mul]
  apply sum_congr rfl
  intro x hx
  rw [(mem_filter.mp hx).2]
  rfl

/-- P.8 for a full shell of 2^n slots, including slots of zero retained weight. -/
theorem shellInteraction_lower {n : ℕ} (q : Shell n → ℚ) :
    2*(1-1/(2:ℚ)^n)*(∑ t, q t)^2 - n*(∑ t, q t^2) ≤
      ∑ t, q t * shellInteraction q t := by
  rw [shellInteraction_eq, sum_sub_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply sub_le_sub_right
  calc
    _ = ∑ s : Fin n, (∑ t, q t)^2 / 2^s.val := by
      rw [Fin.sum_univ_eq_sum_range (fun s => (∑ t, q t)^2 / 2^s)]
      simp_rw [div_eq_mul_inv]
      rw [← mul_sum, ← show (∑ i ∈ range n, (1:ℚ)/2^i) =
          ∑ i ∈ range n, (2^i : ℚ)⁻¹ by simp [one_div], geometric]
      ring
    _ ≤ _ := sum_le_sum fun s _ => classWeight_cauchy q s

/-- The lower bound for the same-shell loss averaged with weights q_t/W. -/
theorem shellAverage_lower {n : ℕ} (q : Shell n → ℚ) (M : ℚ)
    (hq : ∀ x, 0 ≤ q x) (hcap : ∀ x, q x ≤ 4*M) (hW : 0 < ∑ x, q x) :
    2*((2:ℚ)^n-1)*((∑ x, q x)/2^n)-4*M*n ≤
      (∑ t, q t * shellInteraction q t)/(∑ t, q t) := by
  have hs := shellInteraction_lower q
  have hsq : (∑ t, q t^2) ≤ 4*M*(∑ t, q t) := by
    rw [mul_sum]
    apply sum_le_sum
    intro t _
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (hcap t) (hq t)
  have hn := mul_le_mul_of_nonneg_left hsq (show (0:ℚ) ≤ n by positivity)
  apply (le_div_iff₀ hW).2
  calc
    _ = 2*(1-1/(2:ℚ)^n)*(∑ t, q t)^2 - (n:ℚ)*(4*M*(∑ t, q t)) := by
      field_simp
    _ ≤ _ := (sub_le_sub_left hn _).trans hs

/-- P.9 includes empty shells and uses only the bound at retained centers. -/
theorem nodewiseShellBound {u a n : ℕ} (q : Shell n → ℚ) (h M higher : ℚ)
    (hn : n ≤ a) (hdeep : u+1 ≤ n) (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hq : ∀ t, 0 ≤ q t) (hcap : ∀ t, q t ≤ 4*M) (hhigher : 0 ≤ higher)
    (hprecision : ∀ t, 0 < q t →
      shellInteraction q t - (2:ℚ)^n*higher ≤ 8*h*2^n+8*M*(a+1)) :
    2*((∑ t, q t)/2^n)-higher ≤ 8*h+M*(12*a+16)/2^(u+1) := by
  let W : ℚ := ∑ t, q t
  let D : ℚ := 2^n
  let m : ℚ := W/D
  have hD : 0 < D := by dsimp [D]; positivity
  have hW : 0 ≤ W := sum_nonneg fun t _ => hq t
  change 2*m-higher ≤ _
  by_cases hpos : 0 < W
  · have hlow := shellAverage_lower q M hq hcap hpos
    have hsum : (∑ t, q t * shellInteraction q t) ≤
        W * (8*h*D + 8*M*(a+1) + D*higher) := by
      dsimp only [W]
      rw [sum_mul]
      apply sum_le_sum
      intro t _
      by_cases ht : 0 < q t
      · apply mul_le_mul_of_nonneg_left _ (hq t)
        have hp := hprecision t ht
        change shellInteraction q t - D*higher ≤ 8*h*D+8*M*(a+1) at hp
        linarith
      · have hz : q t = 0 := le_antisymm (le_of_not_gt ht) (hq t)
        simp [hz]
    have hup : (∑ t, q t * shellInteraction q t)/W ≤ 8*h*D + 8*M*(a+1) + D*higher :=
      (div_le_iff₀ hpos).2 (by rwa [mul_comm _ W])
    have hbound := averagedShellBound h M D n a m higher
      ((∑ t, q t * shellInteraction q t)/W) hD hlow
      (by linarith only [hup])
    have hm : m ≤ 4*M := by
      apply (div_le_iff₀ hD).2
      calc
        W ≤ ∑ _ : Shell n, 4*M := sum_le_sum fun t _ => hcap t
        _ = 4*M*D := by simp [D, nsmul_eq_mul, mul_comm]
    have hnum : 8*M*(a+1)+4*M*n+2*m ≤ M*(12*a+16) := by
      have hna : (n:ℚ) ≤ a := by exact_mod_cast hn
      nlinarith only [hm, mul_le_mul_of_nonneg_left hna hM]
    have hpow : (2 : ℚ)^(u+1) ≤ D := pow_le_pow_right₀ (by norm_num) hdeep
    refine hbound.trans (add_le_add_left ?_ _)
    exact (div_le_div_of_nonneg_right hnum hD.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow)
  · have hz : W = 0 := le_antisymm (le_of_not_gt hpos) hW
    have hz' : m = 0 := by simp [m, hz]
    rw [hz']
    have hR : 0 ≤ 8*h+M*(12*a+16)/2^(u+1) := by positivity
    linarith

end
end S7
