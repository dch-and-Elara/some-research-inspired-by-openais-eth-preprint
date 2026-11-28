import J1PPrintedDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Appendix D mesh feasibility with the literal Delta = ceil(s^0.9).
The extra integer margins give finite, explicit P8–P11 slack. -/

namespace J1PPrinted

noncomputable def sourceDelta (s : ℕ) : ℕ := ⌈(s:ℝ)^(9/10:ℝ)⌉₊

def deltaExponent (lambda : ℕ) : ℕ := (9*lambda+9)/10

theorem delta_core_power (s : ℕ) : ((s:ℝ)^(9/10:ℝ))^10 = (s:ℝ)^9 := by
  rw [← Real.rpow_mul_natCast (show (0:ℝ) ≤ s by positivity)]
  norm_num

theorem delta_pow_ge (s : ℕ) : s^9 ≤ (sourceDelta s)^10 := by
  have hs := (Nat.le_ceil ((s:ℝ)^(9/10:ℝ)))
  have ht := pow_le_pow_left₀ (Real.rpow_nonneg (show (0:ℝ) ≤ s by positivity) _) hs 10
  rw [delta_core_power] at ht
  exact_mod_cast ht

theorem delta_upper_dyadic (s lambda : ℕ) (hs : s ≤ (2:ℕ)^lambda) :
    sourceDelta s ≤ (2:ℕ)^deltaExponent lambda := by
  have hce : 9*lambda ≤ 10*deltaExponent lambda := by unfold deltaExponent; omega
  have hp : s^9 ≤ ((2:ℕ)^deltaExponent lambda)^10 := by
    calc
      s^9 ≤ ((2:ℕ)^lambda)^9 := Nat.pow_le_pow_left hs _
      _ = (2:ℕ)^(9*lambda) := by rw [← pow_mul,Nat.mul_comm]
      _ ≤ (2:ℕ)^(10*deltaExponent lambda) := Nat.pow_le_pow_right (by decide) hce
      _ = _ := by rw [← Nat.mul_comm, pow_mul]
  unfold sourceDelta
  apply Nat.ceil_le.mpr
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (show (0:ℝ)≤s by positivity) _)
    (by positivity) (by decide : (10:ℕ) ≠ 0)).mp
  rw [delta_core_power]
  exact_mod_cast hp

theorem stepD_dyadic (lambda d : ℕ) : stepD lambda d = 2^(12*stepA lambda d) := by
  rw [stepD_power, stepL, ← pow_mul, Nat.mul_comm]

theorem stepL_pos (lambda d : ℕ) : 0 < stepL lambda d := by unfold stepL; positivity

theorem stepD_pos (lambda d : ℕ) : 0 < stepD lambda d := by rw [stepD_dyadic]; positivity

/-- Stronger than just the printed feasibility. The last three bounds
are respectively the two terms in P8 and the square-root loss in P9,
with explicit shrinking factors. All depths (not only the root) use
the actual printed prefix sum of u_j. -/
theorem mesh_margins (s M d : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M) :
    let lambda := Nat.clog 2 s
    let u := J9PrintedSchedule.rootU lambda
    let L := stepL lambda d
    let D := stepD lambda d
    let Δ := sourceDelta s
    2*D^2*Δ ≤ M ∧ L^3*D ≤ M ∧ 2*L ≤ Δ ∧
      ((2^u)*L*D)^2*2*Δ ≤ M ∧ (2^u)*L^2*D ≤ M ∧
      5*((2:ℕ)^(u+2))^2*D*L ≤ M := by
  dsimp only
  let lam := Nat.clog 2 s
  let u := J9PrintedSchedule.rootU lam
  let a := stepA lam d
  let L := stepL lam d
  let D := stepD lam d
  let k := deltaExponent lam
  let Δ := sourceDelta s
  have hu : 1 ≤ u := hU
  have hlo : 131072*u ≤ lam := (J9PrintedSchedule.rootU_range lam).1
  have ha : a ≤ 4*u := stepA_bound lam d
  have hd : D = (2:ℕ)^(12*a) := stepD_dyadic lam d
  have hL : L = (2:ℕ)^a := rfl
  have hΔ : Δ ≤ (2:ℕ)^k := delta_upper_dyadic s lam (Nat.le_pow_clog (by decide) _)
  have hM := active_wire_lower s M hU active
  change (2:ℕ)^(lam-18-u)<M at hM
  have fits (e : ℕ) (he : e ≤ lam-18-u) : (2:ℕ)^e ≤ M :=
    (Nat.pow_le_pow_right (by decide) he).trans hM.le
  have hk : k=(9*lam+9)/10 := rfl
  have hp8 : ((2:ℕ)^u*L*D)^2*2*Δ ≤ M := by
    calc
      _ ≤ ((2:ℕ)^u*L*D)^2*2*2^k := Nat.mul_le_mul_left _ hΔ
      _ = 2^(2*(u+13*a)+1+k) := by
        rw [hL,hd,← pow_add,← pow_add,← pow_mul]
        have hx : u+a+12*a = u+13*a := by omega
        rw [hx, Nat.mul_comm (u+13*a) 2]
        calc
          ((2:ℕ)^(2*(u+13*a)))*2*2^k =
              ((2:ℕ)^(2*(u+13*a)))*2^1*2^k := by rw [pow_one]
          _ = _ := by rw [← pow_add,← pow_add]
      _ ≤ M := fits _ (by omega)
  refine ⟨?_, ?_, ?_, hp8, ?_, ?_⟩
  · calc
      _ ≤ 2*D^2*2^k := Nat.mul_le_mul_left _ hΔ
      _ = 2^(1+24*a+k) := by
        rw [hd,← pow_mul]
        have hx : 12*a*2 = 24*a := by omega
        rw [hx]
        calc
          2*(2:ℕ)^(24*a)*2^k = 2^1*(2:ℕ)^(24*a)*2^k := by rw [pow_one]
          _ = _ := by rw [← pow_add,← pow_add]
      _ ≤ M := fits _ (by omega)
  · change L^3*D ≤ M
    rw [hL,hd,← pow_mul,← pow_add]
    exact fits _ (by omega)
  · have hs : (2:ℕ)^(lam-1) ≤ s :=
      ((Nat.lt_clog_iff_pow_lt (b:=2) (by decide)).1
        (by change lam-1<lam; omega)).le
    apply (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : (10:ℕ) ≠ 0)).mp
    calc
      (2*L)^10 = 2^(10*(1+a)) := by
        rw [hL]
        calc
          (2*(2:ℕ)^a)^10 = ((2:ℕ)^1*2^a)^10 := by rw [pow_one]
          _ = _ := by rw [← pow_add,← pow_mul,Nat.mul_comm]
      _ ≤ ((2:ℕ)^(lam-1))^9 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ s^9 := Nat.pow_le_pow_left hs _
      _ ≤ Δ^10 := delta_pow_ge s
  · change (2:ℕ)^u*L^2*D ≤ M
    rw [hL,hd,← pow_mul,← pow_add,← pow_add]
    exact fits _ (by omega)
  · calc
      _ ≤ (2:ℕ)^3*((2:ℕ)^(u+2))^2*D*L := by gcongr; decide
      _ = 2^(3+(u+2)*2+12*a+a) := by
        rw [hL,hd,← pow_mul,← pow_add,← pow_add,← pow_add]
      _ ≤ M := fits _ (by omega)

theorem source_packing_conditions (s M d : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M) :
    let L := stepL (Nat.clog 2 s) d
    let D := stepD (Nat.clog 2 s) d
    2*D^2*sourceDelta s ≤ M ∧ L*D ≤ M ∧ 2*L ≤ sourceDelta s := by
  dsimp only
  have h := mesh_margins s M d hU active
  dsimp only at h
  refine ⟨h.1, ?_, h.2.2.1⟩
  apply le_trans _ h.2.1
  exact Nat.mul_le_mul_right _ (by
    simpa using Nat.pow_le_pow_right (stepL_pos (Nat.clog 2 s) d) (show 1≤(3:ℕ) by decide))

#print axioms delta_pow_ge
#print axioms delta_upper_dyadic
#print axioms mesh_margins
#print axioms source_packing_conditions

end J1PPrinted

