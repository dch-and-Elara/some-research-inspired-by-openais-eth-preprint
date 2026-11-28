import J6R15ModeCostExponent
import Mathlib.Data.Nat.Sqrt

/-! Integral square-root optimization and the zero-multiplicity case.
The selected exponent is explicit and still bounds only mode tuples. -/
namespace J6R15ModeCost
open J6R10Repack

theorem optimize_exponent (B p : ℕ) (hB : 0<B) (hBP : B≤p) :
    ∃ k : ℕ, 0<k ∧ 8*B*k+((p-1)/k+1)≤18*Nat.sqrt (B*p) := by
  let q := p/B
  let r := Nat.sqrt q
  let k := r+1
  have hQ : 1≤q := (Nat.le_div_iff_mul_le hB).mpr (by simpa)
  have hR : 0<r := Nat.sqrt_pos.mpr (by omega)
  have hk : 0<k := by unfold k; omega
  have hd : B*q≤p := by
    unfold q
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self p B
  have hsqr : (B*r)*(B*r)≤B*p := by
    calc
      _=B*(B*(r*r)) := by ring
      _≤ B*(B*q) := Nat.mul_le_mul_left B (Nat.mul_le_mul_left B (Nat.sqrt_le q))
      _≤_ := Nat.mul_le_mul_left B hd
  have hbig := Nat.le_sqrt.mpr hsqr
  have hBk : B*k≤2*Nat.sqrt (B*p) := by
    have H : B≤B*r := Nat.le_mul_of_pos_right B hR
    unfold k
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hQk : q+1≤k*k := Nat.succ_le_of_lt (Nat.lt_succ_sqrt q)
  have hPpred : p<B*(q+1) := by
    have H := Nat.mod_add_div p B
    have M := Nat.mod_lt p hB
    change p%B+B*q=p at H
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hPX : p-1<(B*k)*k := by
    have hT := hPpred.trans_le (Nat.mul_le_mul_left B hQk)
    rw [← mul_assoc] at hT
    omega
  have hE : (p-1)/k+1≤B*k := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul hk).mpr hPX)
  refine ⟨k,hk,?_⟩
  have H : 8*B*k=8*(B*k) := by ring
  rw [H]
  omega

theorem no_weight_empty (ws : List ℕ) (h : ∀ w,ws.count w=0) : ws=[] := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    have H := h w
    simp at H

theorem native_sqrt_bound {E R C G : Type*} [Fintype E] [LinearOrder G] [Fintype G]
    {a p : ℕ} {N : Network E R C} (P : PhysicalPacking N a G) (i : Fin a)
    (ms : List (Mode (Crossing (G:=G) (pages:=P.copies) i) (2^(i.val+1)) p))
    (hm : ms.Nodup) (hall : ∀ m,m∈ms) (hp : 0<p) (hP : 6*Nat.card E≤p) :
    let B := (6*Nat.card E)/2^(a-i.val)
    (strictTuples (ms.map modeWeight) p).length≤2^(18*Nat.sqrt (B*p)) := by
  let B := (6*Nat.card E)/2^(a-i.val)
  change (strictTuples (ms.map modeWeight) p).length≤2^(18*Nat.sqrt (B*p))
  by_cases h : B=0
  · have hN (j : ℕ) : (ms.map modeWeight).count j=0 := by
      classical
      rw [roster_weight_count ms hm hall]
      have H := native_weight_multiplicity P i p j
      have HC := (Nat.le_div_iff_mul_le (show 0<2^(a-i.val) by positivity)).mpr H
      change _≤B at HC
      omega
    rw [no_weight_empty _ hN,h]
    simp [strictTuples,hp.ne',enumerate]
  · have hB : 0<B := Nat.pos_of_ne_zero h
    have hBP : B≤p := (Nat.div_le_self _ _).trans hP
    obtain ⟨k,hk,hE⟩ := optimize_exponent B p hB hBP
    exact (native_exponent_bound P i ms hm hall hp k hk).trans (Nat.pow_le_pow_right (by decide) hE)

#print axioms optimize_exponent
#print axioms native_sqrt_bound
end J6R15ModeCost

