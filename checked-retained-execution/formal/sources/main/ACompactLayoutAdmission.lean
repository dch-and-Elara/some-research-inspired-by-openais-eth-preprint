import ACompactLayoutParameters

/-! Arithmetic root admission for the actual A4 padding. We compute
the degree cutoff as the least integer D with s^9 ≤ D^10, an
integer-only characterization of the printed ceil(s^(9/10)). -/
namespace ACompactLayout

def degreeCut (s : ℕ) : ℕ :=
  ((List.range' 0 (s+1)).find? (fun d => decide (s^9≤d^10))).getD s

theorem degreeCut_spec (s : ℕ) :
    s^9 ≤ degreeCut s^10 ∧ ∀ d, s^9≤d^10 → degreeCut s≤d := by
  unfold degreeCut
  let p := fun d : ℕ => decide (s^9≤d^10)
  have hs : s^9 ≤ s^10 := by
    cases s with
    | zero => decide
    | succ s => exact Nat.pow_le_pow_right (by omega) (by decide)
  change s^9 ≤ ((List.range' 0 (s+1)).find? p).getD s^10 ∧ _
  cases h : (List.range' 0 (s+1)).find? p with
  | none =>
    have he := (List.find?_range'_eq_none.mp h) s (by omega) (by omega)
    simp [p,hs] at he
  | some d =>
    obtain ⟨ha,_,hl⟩ := List.find?_range'_eq_some.mp h
    refine ⟨by simpa [p] using ha,?_⟩
    intro r hr
    by_contra hn
    have he := hl r (by omega) (by simpa using hn)
    simp [p,hr] at he

theorem root_packing_admitted (w delta : ℕ) (hdelta : delta≤w)
    (hU : 1≤J9PrintedSchedule.rootU (lambda w)) :
    let Δ := degreeCut (paddedSize w delta)
    total w ≥ 2*(cells w)^2*Δ ∧
    total w ≥ packetLength w*cells w ∧ 2*packetLength w ≤ Δ := by
  let s := paddedSize w delta
  let d := degreeCut s
  let ell := lambda w
  let a := exponent w
  let k := ell-24*a-1
  have hu := (J9PrintedSchedule.rootU_range ell).1
  have ha : a=2*J9PrintedSchedule.rootU ell := rfl
  have hb : 240*a+10≤ell := by
    change 1≤J9PrintedSchedule.rootU ell at hU
    omega
  have hex : ell*9≤k*10 := by dsimp [k]; omega
  have hs : s ≤ total w := Nat.sub_le _ _
  have hcut : s^9≤((2:ℕ)^k)^10 := by
    calc
      _ ≤ (total w)^9 := Nat.pow_le_pow_left hs 9
      _ = (2:ℕ)^(ell*9) := by rw [pow_mul]; rfl
      _ ≤ (2:ℕ)^(k*10) := Nat.pow_le_pow_right (by decide) hex
      _ = _ := pow_mul _ _ _
  have hd := (degreeCut_spec s).2 _ hcut
  have H : 2*(cells w)^2*2^k=total w := by
    have hc : cells w=(2:ℕ)^(a*12) := by
      unfold cells
      rw [J9PrintedSchedule.arrayCard_power,← pow_mul]
    rw [hc, ← pow_mul]
    change (2:ℕ)^1*2^(a*12*2)*2^k=2^ell
    rw [← pow_add,← pow_add]
    congr 1
    dsimp [k]
    omega
  have hlow : 2^(ell-1) < s := by
    apply (Nat.lt_clog_iff_pow_lt (by decide)).1
    rw [padded_lambda w delta hdelta]
    omega
  have hl : (2*packetLength w)^10≤s^9 := by
    have he : 2*packetLength w=(2:ℕ)^(1+a) := by
      rw [pow_add,pow_one]
      rfl
    rw [he, ← pow_mul]
    calc
      _ ≤ (2:ℕ)^((ell-1)*9) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = ((2:ℕ)^(ell-1))^9 := pow_mul _ _ _
      _ ≤ _ := Nat.pow_le_pow_left hlow.le _
  have hd₀ := (degreeCut_spec s).1
  have hc : packetLength w ≤ perCell w := by
    rw [(common_load w).2.1]
    have hcopy : 0 < packetCopies w := by unfold packetCopies; positivity
    simpa using Nat.mul_le_mul_right (packetLength w) (show 1 ≤ packetCopies w from hcopy)
  change total w ≥ 2*(cells w)^2*d ∧ total w ≥ packetLength w*cells w ∧
    2*packetLength w ≤ d
  refine ⟨(Nat.mul_le_mul_left _ hd).trans_eq H, ?_,?_⟩
  · rw [← (common_load w).1]
    simpa only [mul_comm] using Nat.mul_le_mul_left (cells w) hc
  · by_contra hn
    have hh : d^10 < (2*packetLength w)^10 := Nat.pow_lt_pow_left (by omega) (by decide)
    change s^9 ≤ d^10 at hd₀
    exact (hl.trans hd₀).not_gt hh

#print axioms degreeCut_spec
#print axioms root_packing_admitted

end ACompactLayout
