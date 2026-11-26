import J1PPrintedDepth

/-! Remaining exact source-mesh size and taper applicability bounds. -/

namespace J1PPrinted

open scoped BigOperators

theorem stepA_ge_root (lambda d : ℕ) :
    2*J9PrintedSchedule.rootU lambda ≤ stepA lambda d := by
  have h : stepU lambda 0 ≤ ∑ j ∈ Finset.range (d+1), stepU lambda j :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (stepU lambda i))
      (Finset.mem_range.mpr (Nat.zero_lt_succ _))
  simpa [stepA, stepU_as_div] using Nat.mul_le_mul_left 2 h

theorem stepL_ge_four (lambda d : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU lambda) :
    4 ≤ stepL lambda d := by
  have h := stepA_ge_root lambda d
  change (2:ℕ)^2 ≤ 2^stepA lambda d
  exact Nat.pow_le_pow_right (by decide) (by omega)

set_option exponentiation.threshold 12000 in
theorem dimensions_small (s d : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s)) :
    (stepL (Nat.clog 2 s) d)^1000 < s ∧ (stepD (Nat.clog 2 s) d)^1000 < s := by
  let lam := Nat.clog 2 s
  let u := J9PrintedSchedule.rootU lam
  let a := stepA lam d
  have hu : 1 ≤ u := hU
  have hlo : 131072*u ≤ lam := (J9PrintedSchedule.rootU_range lam).1
  have ha : a ≤ 4*u := stepA_bound lam d
  have hs : (2:ℕ)^(lam-1) < s := (Nat.lt_clog_iff_pow_lt (b:=2) (by decide)).1
    (by change lam-1<lam; omega)
  have e1 : a*1000 ≤ lam-1 := by omega
  have e2 : a*12000 ≤ lam-1 := by omega
  refine ⟨?_,?_⟩
  · change ((2:ℕ)^a)^1000 < s
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide) e1).trans_lt hs
  · change (stepD lam d)^1000 < s
    rw [stepD_power, ← pow_mul]
    change ((2:ℕ)^a)^12000 < s
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide) e2).trans_lt hs

theorem lambda_lt_active_wires (s M : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M) :
    Nat.clog 2 s < M := by
  let lam := Nat.clog 2 s
  let u := J9PrintedSchedule.rootU lam
  have hu : 1 ≤ u := hU
  have hlo : 131072*u ≤ lam := (J9PrintedSchedule.rootU_range lam).1
  have hhi : lam < 131072*(u+1) := (J9PrintedSchedule.rootU_range lam).2
  calc
    lam ≤ 131072*(u+1) := hhi.le
    _ ≤ 131072*(2:ℕ)^u := Nat.mul_le_mul_left _ (J9PrintedSchedule.next_le_two_power u)
    _ = (2:ℕ)^(17+u) := (pow_add (2:ℕ) 17 u).symm
    _ ≤ (2:ℕ)^(lam-18-u) := Nat.pow_le_pow_right (by decide) (by omega)
    _ < M := active_wire_lower s M hU active

theorem printed_taper_legal (s M C d : ℕ)
    (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s)) (hC : 0 < C)
    (hsize : (2*epsDen)^30 * C^10 ≤ Nat.clog 2 s)
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (shrink : 8^d*M ≤ C*s) :
    let lam := Nat.clog 2 s
    let u := stepU lam d
    1 ≤ u ∧ u ≤ stepA lam d ∧ u ≤ M := by
  dsimp only
  let lam := Nat.clog 2 s
  let u := stepU lam d
  have h := printed_u_four_fifths s M C d hC hsize active shrink
  have hl : 0<lam := by
    have hp : 0<(2*epsDen)^30*C^10 := by unfold epsDen; positivity
    exact hp.trans_le hsize
  have hu : 1≤u := by
    by_contra! hh
    have he : u=0 := by omega
    change lam^4 ≤ u^5 at h
    rw [he] at h
    exact (not_le_of_gt (pow_pos hl 4)) h
  have hs : u ≤ lam := Nat.div_le_self _ _
  exact ⟨hu,stepA_has_u _ _,hs.trans (lambda_lt_active_wires s M hU active).le⟩

#print axioms dimensions_small
#print axioms stepL_ge_four
#print axioms printed_taper_legal

end J1PPrinted

