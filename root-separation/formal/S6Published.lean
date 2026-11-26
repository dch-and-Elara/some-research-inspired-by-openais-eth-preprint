import S6Matching

namespace Section6

open Filter
open scoped Topology

noncomputable section

def publishedLambda (n : ℕ) : ℕ := ⌈lg (n : ℝ)⌉₊
def publishedNu (lam : ℕ) : ℕ := ⌈lg (lam : ℝ)⌉₊
def publishedRGroups (lam nu : ℕ) : ℕ := ⌊√(lam : ℝ) / (nu : ℝ)^2⌋₊
def publishedQ (lam nu : ℕ) : ℕ := ⌊(lam : ℝ) / (128*(nu : ℝ))⌋₊
def publishedR (b lam : ℕ) : ℕ := (b+3)*⌈√(lam : ℝ)⌉₊

lemma lg_mono {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : lg x ≤ lg y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx h) logTwo_pos.le

lemma lg_pow (x : ℝ) (j : ℕ) : lg (x^j) = (j : ℝ) * lg x := by
  unfold lg
  rw [Real.log_pow, mul_div_assoc]

lemma lg_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : lg (x/y) = lg x - lg y := by
  unfold lg
  rw [Real.log_div hx hy, sub_div]

lemma lg_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : lg (x*y) = lg x + lg y := by
  unfold lg
  rw [Real.log_mul hx hy, add_div]

@[simp] lemma lg_two : lg 2 = 1 := div_self logTwo_pos.ne'

lemma lg_atTop : Tendsto lg atTop atTop := by
  unfold lg
  simp only [div_eq_mul_inv]
  exact Real.tendsto_log_atTop.atTop_mul_const (inv_pos.mpr logTwo_pos)

lemma lambda_atTop : Tendsto publishedLambda atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [(lg_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (k : ℝ)] with n hn
  have ht : (k : ℝ) ≤ (publishedLambda n : ℝ) := hn.trans (Nat.le_ceil _)
  exact_mod_cast ht

lemma nu_atLeast_one (lam : ℕ) (h : 2 ≤ lam) : 1 ≤ publishedNu lam := by
  have ht : (1 : ℝ) ≤ (publishedNu lam : ℝ) := by
    calc
      _ = lg 2 := lg_two.symm
      _ ≤ lg lam := lg_mono (by norm_num) (by exact_mod_cast h)
      _ ≤ _ := Nat.le_ceil _
  exact_mod_cast ht

lemma eventually_nu_pow_le (c : ℝ) (hc : 0 < c) (d : ℕ) (s : ℝ) (hs : 0 < s) :
    ∀ᶠ lam : ℕ in atTop, (publishedNu lam : ℝ)^d ≤ c*(lam : ℝ)^s := by
  let k := 2 / Real.log 2
  have hk : 0 < k := div_pos (by norm_num) logTwo_pos
  have hsmall := (isLittleO_log_rpow_rpow_atTop (d : ℝ) hs).bound (div_pos hc (pow_pos hk d))
  have h' := tendsto_natCast_atTop_atTop (R := ℝ) hsmall
  filter_upwards [h', eventually_ge_atTop (2 : ℕ)] with lam hlog hn
  have hpos : (0 : ℝ) < lam := by exact_mod_cast (show 0 < lam by omega)
  have hlg : 1 ≤ lg lam := lg_two ▸ lg_mono (by norm_num) (by exact_mod_cast hn)
  have hnon : 0 ≤ Real.log (lam : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ lam by omega))
  have hnu := Nat.ceil_lt_add_one (show 0 ≤ lg (lam : ℝ) by linarith)
  have he : (publishedNu lam : ℝ) ≤ k*Real.log lam := by
    change (publishedNu lam : ℝ) < lg lam + 1 at hnu
    dsimp [k,lg] at *
    linarith only [hnu, hlg, show 2/Real.log 2*Real.log lam = 2*(Real.log lam/Real.log 2) by ring]
  change ‖Real.log (lam : ℝ) ^ (d : ℝ)‖ ≤ c/k^d * ‖(lam : ℝ)^s‖ at hlog
  have hb : Real.log (lam : ℝ)^d ≤ (c/k^d)*(lam : ℝ)^s := by
    simpa only [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hnon _),
      Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)] using hlog
  calc
    _ ≤ (k*Real.log lam)^d := pow_le_pow_left₀ (by positivity) he _
    _ = k^d * Real.log (lam : ℝ)^d := mul_pow .. 
    _ ≤ k^d * ((c/k^d)*(lam : ℝ)^s) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp [(pow_pos hk d).ne']

lemma floor_halves {x : ℝ} (hx : 2 ≤ x) :
    x/2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  exact ⟨by linarith [Nat.lt_floor_add_one x], Nat.floor_le (by linarith)⟩

def paperD (Q r : ℕ) := r^(2*Q)

structure Rounded (b lam : ℕ) : Prop where
  hLam : 128 ≤ lam
  hNu : 1 ≤ publishedNu lam
  groups : 2 ≤ publishedRGroups lam (publishedNu lam)
  window : 32 ≤ publishedR b lam
  sep : 6*publishedR b lam ≤ publishedQ lam (publishedNu lam)
  rSq : (publishedRGroups lam (publishedNu lam))^2 ≤ lam
  qMul : publishedQ lam (publishedNu lam) * 128 * publishedNu lam ≤ lam
  rWide : (b+3)^2*lam ≤ (publishedR b lam)^2
  dimLog : lg (paperD (publishedQ lam (publishedNu lam)) (publishedRGroups lam (publishedNu lam))) ≤ (lam : ℝ)/128
  gridLog : lg (2*(paperD (publishedQ lam (publishedNu lam)) (publishedRGroups lam (publishedNu lam)) : ℝ)+1) ≤ lam
  ratio : (publishedR b lam : ℝ)/publishedQ lam (publishedNu lam) ≤
    (512*(b+3) : ℝ)*publishedNu lam/√(lam : ℝ)
  ratioLog : Real.log (1/((publishedR b lam : ℝ)/publishedQ lam (publishedNu lam))) ≤ publishedNu lam
  invGroup : 1/(publishedRGroups lam (publishedNu lam) : ℝ) ≤
    2*(publishedNu lam : ℝ)^2/√(lam : ℝ)

/-- The actual floors and ceiling in the frozen parameter formulas. -/
theorem eventually_rounded (b : ℕ) : ∀ᶠ lam : ℕ in atTop, Rounded b lam := by
  filter_upwards [eventually_ge_atTop (1024 : ℕ),
    eventually_nu_pow_le (1/4) (by norm_num) 2 (1/2) (by norm_num),
    eventually_nu_pow_le (1/256) (by norm_num) 1 1 (by norm_num),
    eventually_nu_pow_le (1/(3072*((b : ℝ)+3))) (by positivity) 1 (1/2) (by norm_num)]
    with lam hbig hrraw hqraw hsep
  rw [← Real.sqrt_eq_rpow] at hrraw hsep
  rw [pow_one, Real.rpow_one] at hqraw
  rw [pow_one] at hsep
  let nu := publishedNu lam
  let r := publishedRGroups lam nu
  let Q := publishedQ lam nu
  let R := publishedR b lam
  let a := √(lam : ℝ)
  let B := (b : ℝ)+3
  have hnu : 1 ≤ nu := nu_atLeast_one lam (by omega)
  have hν : (1 : ℝ) ≤ nu := by exact_mod_cast hnu
  have hL : (1024 : ℝ) ≤ lam := by exact_mod_cast hbig
  have ha : 32 ≤ a := by
    have h := Real.sqrt_le_sqrt hL
    have e : √(1024 : ℝ) = 32 := by rw [show (1024:ℝ)=32^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [e] at h
  have ha₂ : a^2 = (lam : ℝ) := Real.sq_sqrt (by linarith)
  have hν0 : 0 < (nu : ℝ) := by linarith
  have ha0 : 0 < a := by linarith
  have hB : 0 < B := by unfold B; positivity
  have hrr : 4 ≤ a/(nu : ℝ)^2 := (le_div_iff₀ (by positivity)).mpr (by linarith only [hrraw])
  have hqq : 2 ≤ (lam : ℝ)/(128*(nu : ℝ)) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith only [hqraw])
  have hrFloor := floor_halves (by linarith : 2 ≤ a/(nu : ℝ)^2)
  change a/(nu : ℝ)^2/2 ≤ (r : ℝ) ∧ (r : ℝ) ≤ a/(nu : ℝ)^2 at hrFloor
  have hqFloor := floor_halves hqq
  change (lam : ℝ)/(128*(nu : ℝ))/2 ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ (lam : ℝ)/(128*(nu : ℝ)) at hqFloor
  have hR₁ : B*a ≤ (R : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (Nat.le_ceil a) hB.le
    simpa [B,R,a,publishedR] using h
  have hR₂ : (R : ℝ) ≤ 2*B*a := by
    have h := mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one ha0.le).le hB.le
    have hh := mul_le_mul_of_nonneg_left (show a+1 ≤ 2*a by linarith) hB.le
    have hp : (R : ℝ) ≤ B * (2*a) := by simpa [B,R,a,publishedR] using h.trans hh
    linarith only [hp]
  have hr2 : (2 : ℝ) ≤ r := by linarith only [hrr,hrFloor.1]
  have hQ1 : (1 : ℝ) ≤ Q := by linarith only [hqq,hqFloor.1]
  have hR32 : (32 : ℝ) ≤ R :=
    ha.trans ((le_mul_of_one_le_left ha0.le (show 1 ≤ B by unfold B; linarith [show (0 : ℝ) ≤ b by positivity])).trans hR₁)
  have hQlo : (lam : ℝ) ≤ (Q : ℝ)*(256*nu) := by
    have e : (lam : ℝ)/(128*(nu : ℝ))/2 = (lam : ℝ)/(256*(nu : ℝ)) := by ring
    exact (div_le_iff₀ (by positivity)).mp (e ▸ hqFloor.1)
  have hQhi : (Q : ℝ)*128*nu ≤ lam := by
    have h := (le_div_iff₀ (by positivity : 0 < 128*(nu : ℝ))).mp hqFloor.2
    linarith only [h]
  have hQlam : (Q : ℝ) ≤ lam := by
    have h : 1 ≤ 128*(nu : ℝ) := by linarith
    linarith only [hQhi,mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ Q by positivity)]
  have hrsq : (r : ℝ)^2 ≤ lam := by
    have hnu2 : 1 ≤ (nu : ℝ)^2 := by nlinarith only [hν, sq_nonneg ((nu : ℝ)-1)]
    have hrle : (r : ℝ) ≤ a := hrFloor.2.trans (div_le_self ha0.le hnu2)
    exact (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r) hrle 2).trans_eq ha₂
  have hRsq : B^2*(lam : ℝ) ≤ (R : ℝ)^2 := by
    simpa only [mul_pow,ha₂] using pow_le_pow_left₀ (mul_nonneg hB.le ha0.le) hR₁ 2
  have hη : (R : ℝ)/Q ≤ (512*B*(nu : ℝ))/a := by
    have hQpos : (0 : ℝ) < Q := by linarith
    have hbnd := mul_le_mul_of_nonneg_left hQlo (show (0 : ℝ) ≤ 2*B by positivity)
    have he : 2*B*a*a ≤ 512*B*(nu : ℝ)*Q := by
      rw [mul_assoc, ← pow_two, ha₂]
      linarith only [hbnd]
    rw [div_le_div_iff₀ hQpos ha0]
    exact (mul_le_mul_of_nonneg_right hR₂ ha0.le).trans (by linarith only [he])
  have hsep' : 6*(R : ℝ) ≤ Q := by
    have hv : (nu : ℝ)*(3072*B) ≤ a := by
      apply (le_div_iff₀ (by positivity : 0 < 3072*B)).mp
      simpa [div_eq_mul_inv, mul_comm] using hsep
    have hp : (512*B*(nu : ℝ))/a ≤ 1/6 := by
      apply (div_le_iff₀ ha0).mpr
      linarith only [hv]
    have hh := (div_le_iff₀ (show (0 : ℝ) < Q by linarith)).mp (hη.trans hp)
    linarith only [hh]
  have hinv : 1/(r : ℝ) ≤ 2*(nu : ℝ)^2/a := by
    have e : a/(nu : ℝ)^2/2 = a/(2*(nu : ℝ)^2) := by ring
    have htake := (div_le_iff₀ (by positivity : 0 < 2*(nu : ℝ)^2)).mp (e ▸ hrFloor.1)
    apply (div_le_div_iff₀ (show (0 : ℝ) < r by linarith) ha0).mpr
    linarith only [htake]
  have hlnu : lg lam ≤ (nu : ℝ) := Nat.le_ceil _
  have hlogr : 2*lg r ≤ (nu : ℝ) := by
    have ht := lg_mono (show 0 < (r : ℝ)^2 by positivity) hrsq
    rw [lg_pow] at ht
    norm_num at ht
    linarith only [ht,hlnu]
  have hD : (0 : ℝ) < paperD Q r := by unfold paperD; push_cast; positivity
  have hlogD : lg (paperD Q r) ≤ (lam : ℝ)/128 := by
    have he : lg (paperD Q r) = (2*(Q : ℝ))*lg r := by
      unfold paperD; push_cast; rw [lg_pow]; push_cast; ring
    rw [he]
    nlinarith only [hQhi, mul_le_mul_of_nonneg_left hlogr (show (0 : ℝ) ≤ Q by positivity)]
  have hgrid : lg (2*(paperD Q r : ℝ)+1) ≤ lam := by
    have hD1 : (1 : ℝ) ≤ paperD Q r := by
      have h : 2 ≤ r := by exact_mod_cast hr2
      exact_mod_cast (Nat.one_le_pow _ _ (by omega : 0 < r))
    have h := lg_mono (show 0 < 2*(paperD Q r : ℝ)+1 by positivity)
      (show 2*(paperD Q r : ℝ)+1 ≤ 3*paperD Q r by linarith)
    rw [lg_mul (by norm_num) hD.ne'] at h
    have h3 := lg_mono (by norm_num : (0 : ℝ) < 3) (show (3 : ℝ) ≤ 2^2 by norm_num)
    rw [lg_pow, lg_two] at h3
    norm_num at h3
    linarith only [h,h3,hlogD,hL]
  have hratioLog : Real.log (1/((R : ℝ)/Q)) ≤ nu := by
    have he : 1/((R : ℝ)/Q) = (Q : ℝ)/R := by simp [one_div, inv_div]
    rw [he]
    have h := Real.log_le_log
      (show 0 < (Q : ℝ)/R by positivity)
      ((div_le_self (by positivity : (0 : ℝ) ≤ Q) (show (1 : ℝ) ≤ R by linarith)).trans hQlam)
    have hh := (div_le_iff₀ logTwo_pos).mp hlnu
    linarith only [h, hh, mul_le_mul_of_nonneg_left logTwo_le_one (show (0 : ℝ) ≤ nu by positivity)]
  refine ⟨by omega,hnu,by exact_mod_cast hr2,by exact_mod_cast hR32,by exact_mod_cast hsep',
    by exact_mod_cast hrsq, by exact_mod_cast hQhi, ?_,hlogD,hgrid,?_,hratioLog,hinv⟩
  · unfold B at hRsq
    exact_mod_cast hRsq
  · exact hη

#print axioms eventually_rounded
#print axioms lambda_atTop

end
end Section6


