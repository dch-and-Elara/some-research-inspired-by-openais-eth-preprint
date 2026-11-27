import Representative

open scoped BigOperators
open Finset Matrix Polynomial SharpDifference

namespace GrenetResidue

private theorem reduce_linear (s : ℕ) :
    reducePoly (linear s) = if s % 2 = 1 then 1 + X else 1 := by
  have h : linear s = 1 + (s : LocalPoly) * X := by
    rw [linear, Polynomial.C_eq_natCast]
  have hx : reducePoly X = X := Polynomial.map_X _
  rw [h, map_add, map_one, map_mul, hx, reducePoly_natCast]
  by_cases hs : s % 2 = 1
  · simp [hs]
  · have h0 : s % 2 = 0 := by omega
    simp [h0]

theorem reduce_oddFactors (h : ℕ) (E : Fin (2*h) → ℕ) :
    reducePoly (oddFactors h E) = (1 + X) ^ ((deficit h E)^2) := by
  unfold oddFactors
  rw [map_prod]
  simp_rw [map_pow, reduce_linear, show ∀ j : ℕ, (2*j+1) % 2 = 1 from fun j => by omega,
    if_true, Finset.prod_pow_eq_pow_sum]
  simpa using congrArg (fun n : ℕ => ((1 : Polynomial ModTwo) + X) ^ n)
    (sum_center_multiplicities h E 1 (by decide))

theorem reduce_evenFactors (h : ℕ) (E : Fin (2*h) → ℕ) :
    reducePoly (evenFactors h E) = 1 := by
  unfold evenFactors
  rw [map_prod]
  simp_rw [map_pow, reduce_linear, show ∀ j : ℕ, (2*j) % 2 = 0 from fun j => by omega,
    Nat.zero_ne_one, if_false, one_pow, Finset.prod_const_one]

theorem representative_residue (b m : ℕ) :
    reducePoly (normalized (representative b m)) = (1 + X)^ (m^2) := by
  have he := representative_factor_exact b m
  rw [allFactorsQ_split] at he
  rw [liftPoly_injective he, map_mul, reduce_oddFactors, reduce_evenFactors, mul_one,
    representative_deficit]

private noncomputable def nodeProduct (k : ℕ) : LocalPoly :=
  ∏ i : Fin k, linear (2*i.val)

private theorem reduce_nodeProduct (k : ℕ) : reducePoly (nodeProduct k) = 1 := by
  unfold nodeProduct
  rw [map_prod]
  simp_rw [reduce_linear, show ∀ j : ℕ, (2*j) % 2 = 0 from fun j => by omega,
    Nat.zero_ne_one, if_false, Finset.prod_const_one]

theorem normalized_shift_one {k : ℕ} (E : Fin k → ℕ) (hE : Function.Injective E) :
    normalized (fun j => E j + 1) = nodeProduct k * normalized E := by
  have hE' : Function.Injective (fun j => E j + 1) := fun i j h => hE (Nat.add_right_cancel h)
  have hV : exponentV (fun j => E j+1) = exponentV E := by
    unfold exponentV
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    exact Matrix.det_vandermonde_add _ _
  have hd : (sourceMatrix (fun j => E j+1)).det =
      liftPoly (nodeProduct k) * (sourceMatrix E).det := by
    have hl (i : Fin k) : liftPoly (linear (2*i.val)) = 1 + (i.val : UPoly)*twoU := by
      rw [lift_linear, linearQ, Nat.cast_mul, map_mul, Polynomial.C_eq_natCast, twoU]
      simp only [Polynomial.C_eq_natCast, Nat.cast_ofNat]
      ring
    rw [nodeProduct, map_prod]
    convert Matrix.det_mul_column (fun i : Fin k => liftPoly (linear (2*i.val))) (sourceMatrix E) using 1
    congr 1
    apply Matrix.ext
    intro i j
    simp only [sourceMatrix, Matrix.of_apply, hl, pow_succ]
    ring
  rw [normalized_factorization, normalized_factorization, hV] at hd
  apply liftPoly_injective
  rw [map_mul]
  have hU : twoU ≠ 0 := mul_ne_zero (by norm_num) X_ne_zero
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hU) (exponentV_ne_zero hE))
  rw [hd]
  ring

theorem normalized_shift_one_residue {k : ℕ} (E : Fin k → ℕ) (hE : Function.Injective E) :
    reducePoly (normalized (fun j => E j+1)) = reducePoly (normalized E) := by
  rw [normalized_shift_one E hE, map_mul, reduce_nodeProduct, one_mul]

private theorem oddSize_shift_one {k : ℕ} (E : Fin k → ℕ) :
    oddSize (fun j => E j + 1) = evenSize E := by
  classical
  let e : {j // Odd (E j + 1)} ≃ {j // Even (E j)} :=
    Equiv.subtypeEquivRight (fun j => by simp [Nat.odd_iff, Nat.even_iff]; omega)
  exact Fintype.card_congr e


private theorem representative_residue_cast (b m h : ℕ) (hs : b+m = h) :
    reducePoly (normalized (representative b m ∘
      finCongr (congrArg (fun z : ℕ => 2*z) hs.symm))) = (1 + X) ^ (m^2) := by
  subst h
  exact representative_residue b m

theorem normalized_residue (h : ℕ) (E : Fin (2*h) → ℕ) (hE : Function.Injective E) :
    reducePoly (normalized E) = (1 + X) ^ ((deficit h E)^2) := by
  let b := minority E
  let m := deficit h E
  have hs : b + m = h := Nat.add_sub_of_le (minority_le E)
  let castIdx := finCongr (congrArg (fun z : ℕ => 2*z) hs.symm)
  let R : Fin (2*h) → ℕ := representative b m ∘ castIdx
  have hRi : Function.Injective R := (representative_injective b m).comp castIdx.injective
  have hrCount : oddSize R = b := by
    let e : {j // Odd (R j)} ≃ {j // Odd (representative b m j)} :=
      castIdx.subtypeEquiv (fun _ => Iff.rfl)
    exact (Fintype.card_congr e).trans (representative_oddSize b m)
  have hr : reducePoly (normalized R) = (1 + X)^(m^2) := representative_residue_cast b m h hs
  change reducePoly (normalized E) = (1 + X)^(m^2)
  rcases le_total (oddSize E) (evenSize E) with h | h
  · have hb : b = oddSize E := min_eq_right h
    rw [← hr]
    apply normalized_same_odd_count E R hE hRi
    rw [← oddSize_eq_oddCount, ← oddSize_eq_oddCount, hrCount, hb]
  · have hb : b = evenSize E := min_eq_left h
    rw [← normalized_shift_one_residue E hE, ← hr]
    apply normalized_same_odd_count _ R (fun _ _ he => hE (Nat.add_right_cancel he)) hRi
    rw [← oddSize_eq_oddCount, ← oddSize_eq_oddCount, hrCount, oddSize_shift_one, hb]

private theorem odd_nat_unit (j : ℕ) : IsUnit ((2*j+1 : ℕ) : D) := by
  have hj : 0 < 2*j+1 := by omega
  have hodd : ¬ 2 ∣ 2*j+1 := by omega
  have hm : ((2*j+1 : ℕ) : ℚ)⁻¹ ∈ localTwo := by
    rw [mem_localTwo_iff_val, padicValRat.inv, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hodd]
    simp
  let inv : D := ⟨((2*j+1 : ℕ) : ℚ)⁻¹, hm⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨inv, Subtype.ext ?_⟩
  change ((2*j+1 : ℕ) : ℚ) * (((2*j+1 : ℕ) : ℚ)⁻¹) = 1
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hj)

theorem oddFactors_unit_leadingCoeff (h : ℕ) (E : Fin (2*h) → ℕ) :
    IsUnit (oddFactors h E).leadingCoeff := by
  have hlead (j : ℕ) : (linear (2*j+1)).leadingCoeff = ((2*j+1 : ℕ) : D) := by
    unfold linear
    rw [← (C_1 : C (1 : D) = 1), leadingCoeff_add_of_degree_lt]
    · exact leadingCoeff_C_mul_X _
    · rw [degree_C (one_ne_zero' D), degree_C_mul_X ((odd_nat_unit j).ne_zero)]
      exact_mod_cast (show (0 : ℕ) < 1 from by decide)
  unfold oddFactors
  have hprod (j : ℕ) : IsUnit ((linear (2*j+1) ^ multiplicity E (2*j+1)).leadingCoeff) := by
    rw [Polynomial.leadingCoeff_pow, hlead]
    exact (odd_nat_unit j).pow _
  rw [Polynomial.leadingCoeff_prod]
  exact IsUnit.prod_iff.mpr (fun j _ => hprod j)

private theorem local_dvd_of_lift_dvd {p q : LocalPoly} (hp : IsUnit p.leadingCoeff)
    (h : liftPoly p ∣ liftPoly q) : p ∣ q := by
  obtain ⟨u, hu⟩ := hp
  let p' := C (↑u⁻¹ : D) * p
  have hmonic : p'.Monic := by
    change (C (↑u⁻¹ : D) * p).leadingCoeff = 1
    rw [leadingCoeff_C_mul_of_isUnit (u⁻¹).isUnit, ← hu]
    simp
  have h' : liftPoly p' ∣ liftPoly q := by
    have hunit : IsUnit (liftPoly (C (↑u⁻¹ : D))) := ((u⁻¹).isUnit.map Polynomial.C).map liftPoly
    change liftPoly (C (↑u⁻¹ : D) * p) ∣ liftPoly q
    rw [map_mul]
    simpa using mul_dvd_mul (hunit.dvd : liftPoly (C (↑u⁻¹ : D)) ∣ 1) h
  have hlocal : p' ∣ q := (Polynomial.map_dvd_map toRat Subtype.val_injective hmonic).mp h'
  exact (dvd_mul_left p (C (↑u⁻¹ : D))).trans hlocal

theorem normalized_odd_dvd (h : ℕ) (E : Fin (2*h) → ℕ) (hE : Function.Injective E) :
    oddFactors h E ∣ normalized E := by
  apply local_dvd_of_lift_dvd (oddFactors_unit_leadingCoeff h E)
  have hd := allFactorsQ_dvd E hE
  rw [allFactorsQ_split, map_mul] at hd
  exact (dvd_mul_right _ _).trans hd

theorem normalized_odd_part (h : ℕ) (E : Fin (2*h) → ℕ) (hE : Function.Injective E) :
    ∃ A : LocalPoly, normalized E = oddFactors h E * A ∧ reducePoly A = 1 := by
  obtain ⟨A, hA⟩ := normalized_odd_dvd h E hE
  refine ⟨A, hA, ?_⟩
  have he := congrArg reducePoly hA
  rw [normalized_residue h E hE, map_mul, reduce_oddFactors] at he
  have hmonic : ((1 + X : Polynomial ModTwo) ^ ((deficit h E)^2)).Monic := by
    rw [add_comm, ← C_1]
    exact (Polynomial.monic_X_add_C _).pow _
  apply hmonic.isRegular.left
  simpa only [mul_one] using he.symm


/-- The two harmless top centers in centerSet carry no factor. -/
theorem multiplicity_zero_of_large {k : ℕ} (E : Fin k → ℕ) {s : ℕ} (hs : 2*k-2 ≤ s) :
    multiplicity E s = 0 := by
  unfold multiplicity
  rw [HalfBlockCount.pairs_card]
  omega

end GrenetResidue



