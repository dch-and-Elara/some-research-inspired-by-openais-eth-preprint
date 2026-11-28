import J6R10ReachablePrinted
import J6R15ModeCostPrinted

/-! Floor-faithful inequalities needed to absorb the inherited
precision at the extra 2^u factor in each positive printed centre. -/
namespace J6R16ModeCost
open scoped BigOperators
open J1PPrinted J6ActiveSchedule J6R15ModeCost

def priorBits (lam d : ℕ) : ℕ := 2*∑ k∈Finset.range d,stepU lam k

@[simp] theorem priorBits_zero (lam : ℕ) : priorBits lam 0=0 := by
  simp [priorBits]

theorem priorBits_next (lam d : ℕ) : priorBits lam (d+1)=stepA lam d := rfl

theorem bits_split (lam d : ℕ) : stepA lam d=priorBits lam d+2*stepU lam d := by
  unfold priorBits stepA
  rw [Finset.sum_range_succ,Nat.mul_add]

theorem bits_le_lam (lam d : ℕ) : stepA lam d≤lam := by
  have h := stepA_bound lam d
  have H := (J9PrintedSchedule.rootU_range lam).1
  omega

theorem u_le_lam (lam d : ℕ) : stepU lam d≤lam := Nat.div_le_self _ _

theorem center_level (a M u : ℕ) {t : ℤ} (h : t∈active a M u) :
    padicValInt 2 t<u := by
  by_contra! H
  have hp := active_order_pos a M u t h
  unfold order at hp
  rw [Nat.sub_eq_zero_of_le H,Nat.mul_zero] at hp
  omega

theorem scale_at_center (lam d i : ℕ) (h : i<stepU lam d) :
    2^stepA lam d / 2^i=2^(stepA lam d-i) ∧
    2^(priorBits lam d+stepU lam d)≤2^(stepA lam d-i) ∧
    2^(stepA lam d-i)≤2^stepA lam d := by
  have hs := bits_split lam d
  refine ⟨native_tile_scale _ _ (by omega),?_,?_⟩
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · exact Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)

/-- An elementary integer-only proof with an explicit base threshold.
Avoid treating exp domination as a free asymptotic estimate. -/
theorem sixteen_pow5_le (u : ℕ) (hu : 32≤u) : 16*u^5≤(2:ℕ)^u := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hu
  clear hu
  induction v with
  | zero => decide
  | succ v ih =>
    let n := 32+v
    have H : (n+1)*32≤n*33 := by
      unfold n
      omega
    have HH := Nat.pow_le_pow_left H 5
    rw [mul_pow,mul_pow] at HH
    have hNum : (33:ℕ)^5≤2*32^5 := by decide
    have hnext : (n+1)^5≤2*n^5 := by
      have hCross : (n+1)^5*32^5 ≤ (2*n^5)*32^5 := by
        calc
          (n+1)^5*32^5 ≤ n^5*33^5 := HH
          _ ≤ n^5*(2*32^5) := Nat.mul_le_mul_left _ hNum
          _ = (2*n^5)*32^5 := by ring
      exact Nat.le_of_mul_le_mul_right hCross (by decide : 0<(32:ℕ)^5)
    change 16*(n+1)^5≤(2:ℕ)^(n+1)
    rw [pow_succ]
    calc
      _≤16*(2*n^5) := Nat.mul_le_mul_left _ hnext
      _=(16*n^5)*2 := by ring
      _≤_ := Nat.mul_le_mul_right _ ih

theorem enough_u (lam u : ℕ) (hLam : 1024≤lam) (h : lam^4≤u^5) :
    32≤u := by
  by_contra! hj
  have hl : (1024:ℕ)^4≤lam^4 := Nat.pow_le_pow_left hLam 4
  have hu : u^5≤(31:ℕ)^5 := Nat.pow_le_pow_left (by omega) 5
  have hn : (31:ℕ)^5 < 1024^4 := by decide
  exact (not_le_of_gt hn) (hl.trans (h.trans hu))

theorem dominant_dyadic (lam u : ℕ) (hLam : 1024≤lam) (h : lam^4≤u^5) :
    (lam+1)^4≤(2:ℕ)^u := by
  calc
    (lam+1)^4≤(2*lam)^4 := Nat.pow_le_pow_left (by omega) 4
    _=16*lam^4 := by rw [mul_pow]; rfl
    _≤16*u^5 := Nat.mul_le_mul_left _ h
    _≤_ := sixteen_pow5_le u (enough_u lam u hLam h)

theorem cutoff_scale (s lam M : ℕ) (hLam : 0<lam)
    (ha : J9PrintedSchedule.leafThreshold s lam<M) :
    s≤M*lam := by
  have H := J9PrintedSchedule.le_roundup_mul s lam.sqrt (Nat.sqrt_pos.mpr hLam)
  change s≤J9PrintedSchedule.leafThreshold s lam*lam.sqrt at H
  exact H.trans (Nat.mul_le_mul ha.le (Nat.sqrt_le_self _))

theorem precision_increment_bound (lam d M s C p : ℕ) {t : ℤ}
    (hu : 0<stepU lam d) (huM : stepU lam d≤M) (hM : M≤C*s) :
    childPrecision p (stepA lam d) M (stepU lam d) t≤
      p+(40*C*s*(lam+1))*2^stepA lam d := by
  let u := stepU lam d
  let a := stepA lam d
  let L := (2:ℕ)^a
  let D := L/2^(padicValInt 2 t)
  let H := height M u
  have hu' : 1≤u := hu
  have hH := (Nat.mul_le_mul_left H hu').trans (height_bounds M u hu huM).2
  rw [mul_one] at hH
  have hCoef : H≤4*(C*s) := hH.trans (Nat.mul_le_mul_left 4 hM)
  have hD : D≤L := Nat.div_le_self _ _
  have hL : 1≤L := Nat.succ_le_of_lt (by unfold L; positivity)
  have hA : a+1≤lam+1 := Nat.succ_le_succ (bits_le_lam lam d)
  change p+8*H*D+8*M*(a+1)≤p+(40*C*s*(lam+1))*L
  calc
    _ ≤ p+8*(4*(C*s))*L+8*(C*s)*(lam+1) :=
      Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hCoef) hD) _)
        (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hM) hA)
    _ ≤ p+(8*(4*(C*s))*(lam+1))*L+(8*(C*s)*(lam+1))*L := by
      have h₁ := Nat.mul_le_mul_right L
        (Nat.le_mul_of_pos_right (8*(4*(C*s))) (by omega : 0<lam+1))
      have h₂ := Nat.le_mul_of_pos_right (8*(C*s)*(lam+1)) hL
      exact Nat.add_le_add (Nat.add_le_add_left h₁ _) h₂
    _ = _ := by ring

#print axioms bits_split
#print axioms bits_le_lam
#print axioms center_level
#print axioms scale_at_center
#print axioms dominant_dyadic
#print axioms cutoff_scale
#print axioms precision_increment_bound
end J6R16ModeCost


