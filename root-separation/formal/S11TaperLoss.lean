
import S11ShellCounts
import S11NativeKernel

noncomputable section
namespace S11
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem level_sub_small {x y : ℤ} (hx : x ≠ 0)
    (h : level x < level y) : level (x-y) = level x := by
  have hne : x-y ≠ 0 := by
    intro hh
    have he := sub_eq_zero.1 hh
    rw [he] at h
    omega
  let i := level x
  have dx : (2:ℤ)^i ∣ x := padicValInt_dvd (p:=2) x
  have dy : (2:ℤ)^(i+1) ∣ y := (padicValInt_dvd_iff (p:=2) (i+1) y).2 (Or.inr h)
  have dlo : (2:ℤ)^i ∣ x-y := dvd_sub dx ((pow_dvd_pow _ (Nat.le_succ i)).trans dy)
  have hlow := ((padicValInt_dvd_iff (p:=2) i (x-y)).1 dlo).resolve_left hne
  apply le_antisymm _ hlow
  by_contra! hh
  have dd : (2:ℤ)^(i+1) ∣ x-y := (padicValInt_dvd_iff (p:=2) (i+1) (x-y)).2 (Or.inr hh)
  have hbad := dvd_add dd dy
  rw [sub_add_cancel] at hbad
  have hs := ((padicValInt_dvd_iff (p:=2) (i+1) x).1 hbad).resolve_left hx
  change i+1 ≤ i at hs
  omega

def taperWeight (h u i : ℕ) : ℚ := (h:ℚ) * ((u-i:ℕ):ℚ)

def nonzeroWeight (h u : ℕ) (q : ℤ) : ℚ :=
  if q = 0 then 0 else taperWeight h u (level q)

private theorem weight_difference (h u i j : ℕ) (hij : i ≤ j) :
    -(h:ℚ)*((j-i:ℕ):ℚ) ≤ taperWeight h u j - taperWeight h u i := by
  have hh : u-i ≤ (u-j)+(j-i) := by omega
  have hh' : ((u-i:ℕ):ℚ) ≤ ((u-j:ℕ):ℚ) + ((j-i:ℕ):ℚ) := by exact_mod_cast hh
  unfold taperWeight
  nlinarith only [mul_le_mul_of_nonneg_left hh' (by positivity : (0:ℚ) ≤ h)]

private theorem offset_sum {a : ℕ} {t : ℤ} (ht : t ∈ grid (2^a)) (h u : ℕ) :
    (∑ q ∈ (grid (2^a)).erase t, nonzeroWeight h u q * ((level q:ℚ)-level t)) =
      ∑ q ∈ (grid (2^a)).erase t, taperWeight h u (level (t-q)) * ((level (t-q):ℚ)-level t) := by
  classical
  rw [valuation_multiset ht (fun k => taperWeight h u k * ((k:ℚ)-level t))]
  let F := fun q : ℤ => nonzeroWeight h u q * ((level q:ℚ)-level t)
  have hzero : F 0 = 0 := by simp [F,nonzeroWeight]
  have htzero : F t = 0 := by simp [F]
  have he (q) (hq : q ∈ grid (2^a)) (hz : F q = 0) :
      (∑ x ∈ (grid (2^a)).erase q,F x) = ∑ x ∈ grid (2^a),F x := by
    have hh := Finset.sum_erase_add _ F hq
    simpa [hz] using hh
  calc
    _ = ∑ q ∈ grid (2^a), F q := he t ht htzero
    _ = ∑ q ∈ (grid (2^a)).erase 0, F q := (he 0 (zero_mem_grid a) hzero).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [F,nonzeroWeight,(Finset.mem_erase.1 hq).1]

/-- The actual full-grid tapered loss. Inactive points and zero carry
    zero weight; no estimate about the loss is assumed. -/
theorem tapered_cardinal_loss {a : ℕ} {t : ℤ} (ht : t ∈ grid (2^a)) (ht0 : t ≠ 0)
    (h u : ℕ) :
    -6*(h:ℚ)*(2:ℚ)^(a-level t) ≤
      ∑ q ∈ (grid (2^a)).erase t, nonzeroWeight h u q * ((level q:ℚ)-level (t-q)) := by
  let i := level t
  let s := (grid (2^a)).erase t
  have hpoint (q : ℤ) (hq : q ∈ s) :
      -(h:ℚ)*((level (t-q)-i:ℕ):ℚ)^2 ≤
        (taperWeight h u (level (t-q)) - nonzeroWeight h u q) *
          ((level (t-q):ℚ) - i) := by
    let j := level (t-q)
    change -(h:ℚ)*((j-i:ℕ):ℚ)^2 ≤
      (taperWeight h u j - nonzeroWeight h u q) * ((j:ℚ) - i)
    have hd : t-q ≠ 0 := sub_ne_zero.2 (Finset.mem_erase.1 hq).1.symm
    rcases lt_trichotomy j i with hj|hj|hj
    · have hq0 : q ≠ 0 := by
        intro he
        subst q
        simp [j,i] at hj
      have h1 := level_sub_small hd hj
      have h2 : level ((t-q)-t) = level q := by
        rw [show t-q-t = -q by ring]
        exact S7.v2_neg q
      rw [h2] at h1
      simp [nonzeroWeight,hq0,h1,Nat.sub_eq_zero_of_le hj.le,j]
    · simp [hj]
    · have h1 := level_sub_small ht0 hj
      have hq0 : q ≠ 0 := by
        intro he
        subst q
        simp [j,i] at hj
      have he : level q = i := by simpa [i,show t-(t-q)=q by ring] using h1
      have hw := weight_difference h u i j hj.le
      have hk : (↑(j-i):ℚ) = (j:ℚ)-i := by exact_mod_cast (Nat.cast_sub hj.le : (↑(j-i):ℚ) = _)
      rw [nonzeroWeight,if_neg hq0,he,← hk]
      nlinarith only [mul_le_mul_of_nonneg_right hw (by positivity : (0:ℚ)≤(↑(j-i):ℚ))]
  have hid : (∑ q ∈ s, nonzeroWeight h u q * ((level q:ℚ)-level (t-q))) =
      ∑ q ∈ s, (taperWeight h u (level (t-q)) - nonzeroWeight h u q) *
        ((level (t-q):ℚ)-i) := by
    have he := offset_sum ht h u
    change (∑ q ∈ s, nonzeroWeight h u q * ((level q:ℚ)-i)) =
      ∑ q ∈ s, taperWeight h u (level (t-q)) * ((level (t-q):ℚ)-i) at he
    simp_rw [sub_mul,mul_sub,Finset.sum_sub_distrib] at he ⊢
    linarith
  change _ ≤ ∑ q ∈ s, _
  rw [hid]
  refine le_trans ?_ (Finset.sum_le_sum hpoint)
  rw [← Finset.mul_sum]
  have hm := (valuation_multiset ht (fun j => ((j-i:ℕ):ℚ)^2)).trans_le
    (excess_second_moment (level_grid ht ht0))
  change (∑ q ∈ s, ((level (t-q)-i:ℕ):ℚ)^2) ≤ 6 * (2:ℚ)^(a-i) at hm
  nlinarith only [mul_le_mul_of_nonneg_left hm (by positivity : (0:ℚ)≤h)]

#print axioms level_sub_small
#print axioms tapered_cardinal_loss

end S11

