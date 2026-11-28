import J6Mesh
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Floor

/-! The balanced child sizes of the large J6 layout violate the printed
direct-leaf cutoff. This is a boundary on the leaf decoder, not a
complexity lower bound for contraction. -/
namespace J6R9ZeroCutoff

noncomputable def cutoff (s lam : ℕ) : ℕ := Nat.ceil ((s:ℚ)/(Nat.sqrt lam : ℕ))

/-- The exact ceil/floor cutoff, not its asymptotic approximation. -/
theorem balanced_above_cutoff (s M lam n : ℕ)
    (hs : s ≤ M) (hl : 64^2 ≤ lam) (hM : 64 < M) (hn : 32*n=M) :
    cutoff s lam < n := by
  have hsqrt : 64 ≤ Nat.sqrt lam := Nat.le_sqrt'.2 hl
  have htwo : 2 ≤ n := by omega
  have hSq : (64:ℚ) ≤ (Nat.sqrt lam : ℕ) := by exact_mod_cast hsqrt
  have hpos : (0:ℚ) < (Nat.sqrt lam : ℕ) := by linarith
  have hQ : (s:ℚ) ≤ 32*(n:ℚ) := by
    have hh : s ≤ 32*n := by omega
    exact_mod_cast hh
  have hg : (32:ℚ)*n ≤ ((n-1:ℕ):ℚ)*64 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
    have hq : (2:ℚ) ≤ n := by exact_mod_cast htwo
    linarith
  have hc : cutoff s lam ≤ n-1 := by
    unfold cutoff
    apply Nat.ceil_le.2
    apply (div_le_iff₀ hpos).2
    exact hQ.trans (hg.trans (mul_le_mul_of_nonneg_left hSq (by positivity)))
  omega

/-- At the actual J6 root size, every group with M/32 real child wires
is an active call, irrespective of the value of the probe. -/
theorem actual_J6_balanced_above_cutoff
    (m native n : ℕ) (hs : native ≤ m) (hn : 32*n=J6Mesh.M m) :
    cutoff (J6Mesh.physicalSize m native) (Nat.clog 2 (J6Mesh.physicalSize m native)) < n := by
  obtain ⟨_,hupper,hlog⟩ := J6Mesh.physicalSize_ceiling m native hs
  rw [hlog]
  have hb := J6Mesh.b_pos m
  have hlarge : 4096 ≤ J6Mesh.lambda m := by unfold J6Mesh.lambda; omega
  have hM : 64 < J6Mesh.M m := by
    have ht : (2:ℕ)^7 ≤ (2:ℕ)^J6Mesh.lambda m :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact (show 64 < (2:ℕ)^7 by decide).trans_le ht
  exact balanced_above_cutoff _ _ _ _ hupper hlarge hM hn

#print axioms balanced_above_cutoff
#print axioms actual_J6_balanced_above_cutoff
end J6R9ZeroCutoff
