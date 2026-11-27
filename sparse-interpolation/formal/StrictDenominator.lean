import StrictLocal

namespace GrenetStrict

/-- A positive reduced denominator larger than two either has an odd prime divisor
or is divisible by four. -/
theorem denominator_prime (B : ℕ) (hB : 2 < B) :
    ∃ p : ℕ, p.Prime ∧ p ∣ B ∧ (2 < p ∨ p = 2 ∧ 4 ∣ B) := by
  by_cases h4 : 4 ∣ B
  · exact ⟨2, Nat.prime_two, dvd_trans (by decide) h4, Or.inr ⟨rfl, h4⟩⟩
  · by_cases h2 : 2 ∣ B
    · obtain ⟨a, ha⟩ := h2
      obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (n := a) (by omega)
      have hpb : p ∣ B := by rw [ha]; exact dvd_mul_of_dvd_right hpa _
      have hne : p ≠ 2 := by
        intro he
        subst p
        obtain ⟨r, hr⟩ := hpa
        exact h4 ⟨r, by omega⟩
      exact ⟨p, hp, hpb, Or.inl (lt_of_le_of_ne hp.two_le hne.symm)⟩
    · obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := B) (by omega)
      have hne : p ≠ 2 := fun h => h2 (h ▸ hd)
      exact ⟨p, hp, hd, Or.inl (lt_of_le_of_ne hp.two_le hne.symm)⟩

theorem den_gt_two_of_nonhalf (z : ℚ) (hz : ¬ ∃ a : ℤ, 2*z = (a : ℚ)) :
    2 < z.den := by
  by_contra! hb
  have hp := z.den_pos
  have hcases : z.den = 1 ∨ z.den = 2 := by omega
  apply hz
  have h : 2*z = 2*((z.num : ℚ)/(z.den : ℚ)) := congrArg (fun q : ℚ => 2*q) z.num_div_den.symm
  rcases hcases with hd | hd
  · refine ⟨2*z.num, ?_⟩
    rw [h, hd]
    norm_num
  · refine ⟨z.num, ?_⟩
    rw [h, hd]
    push_cast
    ring

theorem inverse_val_of_dvd_den (p : ℕ) [Fact p.Prime] (z : ℚ) (hd : p ∣ z.den) :
    padicValRat p z⁻¹ = (padicValNat p z.den : ℤ) := by
  have hp : p.Prime := Fact.out
  have hn : ¬ (p : ℤ) ∣ z.num := by
    intro h
    have hn' : p ∣ z.num.natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr h
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes z.reduced hn' hd)
  rw [padicValRat.inv, padicValRat_def, padicValInt.eq_zero_of_not_dvd hn]
  simp

theorem exists_strict_prime_of_den (z : ℚ) (hz : 2 < z.den) :
    ∃ p : ℕ, p.Prime ∧ StrictStep p z⁻¹ := by
  obtain ⟨p, hp, hd, hcases⟩ := denominator_prime z.den hz
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, ?_⟩
  unfold StrictStep
  rw [inverse_val_of_dvd_den p z hd]
  rcases hcases with ho | ⟨rfl, h4⟩
  · have h₁ := one_le_padicValNat_of_dvd z.den_ne_zero hd
    have h₁' : (1 : ℤ) ≤ (padicValNat p z.den : ℤ) := by exact_mod_cast h₁
    have h₂ : (1 : ℤ) < ((p-1 : ℕ) : ℤ) := by
      exact_mod_cast (show 1 < p-1 by omega)
    have hb := mul_le_mul_of_nonneg_left h₁' (show (0 : ℤ) ≤ ((p-1 : ℕ) : ℤ) by positivity)
    linarith
  · have hv : 2 ≤ padicValNat 2 z.den := (padicValNat_dvd_iff_le z.den_ne_zero).mp
      (by simpa using h4 : 2^2 ∣ z.den)
    have hv' : (2 : ℤ) ≤ (padicValNat 2 z.den : ℤ) := by exact_mod_cast hv
    norm_num
    omega

theorem exists_strict_prime (z : ℚ) (hz : ¬ ∃ a : ℤ, 2*z = (a : ℚ)) :
    ∃ p : ℕ, p.Prime ∧ StrictStep p z⁻¹ :=
  exists_strict_prime_of_den z (den_gt_two_of_nonhalf z hz)

end GrenetStrict

