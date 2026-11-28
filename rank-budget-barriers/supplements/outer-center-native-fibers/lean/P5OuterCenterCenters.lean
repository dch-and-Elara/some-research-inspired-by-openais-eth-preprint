import P5HybridDUnclonedRoot
import J6R10ProbeFieldZero

set_option warningAsError true
set_option maxHeartbeats 9000000
namespace Paper5.OuterCenters
open scoped BigOperators Classical Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes HybridDUncloned HybridClosure
  J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R9Recursive P1DyadicGrid J9PrintedSchedule

/-- The inner endpoint of each positive outer interval is an actual source
center as soon as the window contains the offset 2^j. -/
theorem positive_outer_active (a M u K j : ℕ)
    (hM : 0 < M) (hj : j < u) (hw : u ≤ a) (hK : 2^j ≤ K) :
    ∃ t : ℤ, t ∈ J6ActiveSchedule.active a M u ∧ padicValInt 2 t = j ∧
      ((2^a : ℕ) : ℤ) - K ≤ t := by
  have hja : j < a := hj.trans_le hw
  let t := pow₂ a - pow₂ j
  have hf : t = pow₂ j * (pow₂ (a-j) - 1) := by
    unfold t pow₂
    have ha : j + (a-j) = a := by omega
    rw [← ha, pow_add]
    have hs : j + (a - j) - j = a-j := by omega
    rw [hs]
    ring
  have he : Even (pow₂ (a-j)) := by
    have hpos : 0 < a-j := by omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    rw [hk]
    unfold pow₂
    rw [pow_succ]
    exact even_two.mul_left _
  have hodd : Odd (pow₂ (a-j) - 1) := he.sub_odd (by decide)
  have hval : padicValInt 2 t = j := hf ▸ valuation_pow₂_mul_odd j hodd
  have htpos : 0 < t := by
    unfold t
    exact sub_pos.mpr (pow_lt_pow_right₀ (by decide : (1:ℤ)<2) hja)
  have htbound : t < pow₂ a := sub_lt_self _ (pow₂_pos j)
  have hgrid : t ∈ grid a :=
    mem_grid.mpr ⟨by have hp := pow₂_pos a; linarith, htbound⟩
  have hheight : 0 < height M u := by
    have hh : 1 ≤ height M u := (Nat.le_div_iff_mul_le (by omega : 0 < u)).mpr (by omega)
    omega
  refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨htpos.ne',hgrid⟩, ?_⟩, hval, ?_⟩
  · unfold J6ActiveSchedule.order
    rw [hval]
    exact Nat.mul_pos hheight (Nat.sub_pos_of_lt hj)
  · change ((2^a : ℕ) : ℤ) - K ≤ pow₂ a - pow₂ j
    unfold pow₂
    push_cast
    exact sub_le_sub_left (by exact_mod_cast hK) _

theorem outer_fraction_window (u : ℕ) (hu : 10 ≤ u) :
    let a := 2*u
    let K := 2^(a-10)
    1024*K = 2^a ∧ ∀ j < u, 2^j ≤ K := by
  dsimp only
  constructor
  · rw [show (1024 : ℕ) = 2^10 by decide, ← pow_add]
    congr 1
    omega
  · intro j hj
    apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    omega

#print axioms outer_fraction_window
#print axioms positive_outer_active
end Paper5.OuterCenters


