import HermiteLossReflection

/-! Exactly 2^(a-i) nonzero grid representatives at valuation i,
including the top level where the only representative is -2^a. -/

namespace HermiteLoss
open P1DyadicGrid
open scoped BigOperators

def levelCell (a i : ℕ) : Finset ℤ :=
  (grid a).filter fun q => q≠0 ∧ level q=i

theorem mem_levelCell {a i : ℕ} {q : ℤ} :
    q∈levelCell a i ↔ q∈grid a ∧ q≠0 ∧ level q=i := Finset.mem_filter

theorem rep_ne_zero_of_small {a : ℕ} {r : ℤ} (hr0 : 0<r) (hr : r < pow₂ (a+1)) :
    rep a r ≠ 0 := by
  intro h
  have hd := (rep_mod a r).dvd
  rw [h,sub_zero] at hd
  exact hr0.ne' (Int.eq_zero_of_dvd_of_nonneg_of_lt hr0.le hr hd)

theorem level_residue {a : ℕ} {q : ℤ} (hq : q∈grid a) (h0 : q≠0) :
    level (q % pow₂ (a+1))=level q := by
  let B := pow₂ (a+1)
  have hb : 0<B := pow₂_pos _
  let r := q % B
  have hr0 : 0≤r := Int.emod_nonneg _ hb.ne'
  have hr1 : r<B := Int.emod_lt_of_pos _ hb
  have hm : r ≡ q [ZMOD B] := Int.mod_modEq _ _
  have hn : r≠0 := by
    intro h
    rw [h] at hm
    exact h0 (grid_modEq_injective (zero_mem_grid a) hq hm).symm
  have hv : level r ≤ a := by
    by_contra! he
    have hd : B ∣ r := (padicValInt_dvd_iff (p:=2) (a+1) r).mpr (Or.inr he)
    exact hn (Int.eq_zero_of_dvd_of_nonneg_of_lt hr0 hr1 hd)
  exact valuation_eq_of_modEq_pow₂ hm hn h0 (hv.trans (Nat.le_succ _))
    ((level_grid_le hq h0).trans (Nat.le_succ _))

theorem bound_factor {a i : ℕ} (hi : i≤a) :
    pow₂ (a+1) = pow₂ i*((2:ℤ)^(a-i))*2 := by
  rw [pow₂_succ,pow₂,pow₂,← pow_add,Nat.add_sub_of_le hi]

theorem level_card {a i : ℕ} (hi : i≤a) : (levelCell a i).card = 2^(a-i) := by
  let N : ℕ := 2^(a-i)
  let B := pow₂ (a+1)
  let v (j : ℕ) : ℤ := pow₂ i*(2*(j:ℤ)+1)
  let f (j : ℕ) : ℤ := rep a (v j)
  have hB : 0<B := pow₂_pos _
  have hiP : 0<pow₂ i := pow₂_pos _
  have hb : B = pow₂ i*((N:ℕ):ℤ)*2 := by
    change pow₂ (a+1) = pow₂ i*((2^(a-i):ℕ):ℤ)*2
    push_cast
    exact bound_factor hi
  have hbound {j : ℕ} (hj : j<N) : 0<v j ∧ v j<B := by
    have hj' : (j:ℤ)<N := by exact_mod_cast hj
    dsimp [v]
    refine ⟨mul_pos hiP (by omega),?_⟩
    rw [hb,mul_assoc]
    exact mul_lt_mul_of_pos_left (by omega) hiP
  have hv {j : ℕ} : level (v j)=i := by
    apply valuation_pow₂_mul_odd
    exact ⟨(j:ℤ), by ring⟩
  change (levelCell a i).card = N
  rw [← Finset.card_range N]
  symm
  refine Finset.card_bij (fun j _ => f j) ?_ ?_ ?_
  · intro j hj
    have hbnd := hbound (Finset.mem_range.mp hj)
    have h0 := rep_ne_zero_of_small hbnd.1 hbnd.2
    have hiR : level (f j) ≤ a := level_grid_le (rep_mem a _) h0
    have hlo : level (v j) ≤ a+1 := hv.trans_le (hi.trans (Nat.le_succ _))
    have he := valuation_eq_of_modEq_pow₂ (rep_mod a (v j)) h0 hbnd.1.ne'
      (hiR.trans (Nat.le_succ _)) hlo
    exact mem_levelCell.mpr ⟨rep_mem a _,h0,he.trans hv⟩
  · intro j hj k hk he
    change f j = f k at he
    have hm : f j ≡ v k [ZMOD B] := by rw [he]; exact rep_mod a (v k)
    have hh : v j ≡ v k [ZMOD B] := (rep_mod a (v j)).symm.trans hm
    have h1 := hbound (Finset.mem_range.mp hj)
    have h2 := hbound (Finset.mem_range.mp hk)
    have heq := hh.eq
    rw [Int.emod_eq_of_lt h1.1.le h1.2,Int.emod_eq_of_lt h2.1.le h2.2] at heq
    change pow₂ i*(2*(j:ℤ)+1)=pow₂ i*(2*(k:ℤ)+1) at heq
    have he' := mul_left_cancel₀ hiP.ne' heq
    omega
  · intro q hq
    obtain ⟨hq0,hq1,hq2⟩ := mem_levelCell.mp hq
    let r := q%B
    have hmr : r ≡ q [ZMOD B] := Int.mod_modEq _ _
    have hr0 : 0≤r := Int.emod_nonneg _ hB.ne'
    have hrB : r<B := Int.emod_lt_of_pos _ hB
    have hrnz : r≠0 := by
      intro h
      rw [h] at hmr
      exact hq1 (grid_modEq_injective (zero_mem_grid a) hq0 hmr).symm
    have hlev : level r=i := (level_residue hq0 hq1).trans hq2
    obtain ⟨w,ho,he⟩ := integer_odd_factor hrnz
    change r=pow₂ (level r)*w at he
    rw [hlev] at he
    obtain ⟨k,hk⟩ := ho
    have hw : 0<w := by
      by_contra! hn
      have hh : r≤0 := by rw [he]; exact mul_nonpos_of_nonneg_of_nonpos hiP.le hn
      exact hrnz (le_antisymm hh hr0)
    have hk0 : 0≤k := by omega
    have hrk : pow₂ i * (2*k+1) < pow₂ i * (2*(N:ℤ)) := by
      calc
        _ = r := by rw [he,hk]
        _ < B := hrB
        _ = _ := by rw [hb]; ring
    have hkN : k<(N:ℤ) := by
      have h := (mul_lt_mul_iff_right₀ hiP).mp hrk
      omega
    let j := k.toNat
    have hj : (j:ℤ)=k := Int.toNat_of_nonneg hk0
    have hN : j<N := by exact_mod_cast (hj ▸ hkN)
    have hvj : v j=r := by dsimp only [v]; rw [hj,he,hk]
    refine ⟨j,Finset.mem_range.mpr hN,?_⟩
    have hmj : v j ≡ q [ZMOD B] := by rw [hvj]; exact hmr
    exact grid_modEq_injective (rep_mem a _) hq0 ((rep_mod a _).trans hmj)

#print axioms level_residue
#print axioms level_card
end HermiteLoss

