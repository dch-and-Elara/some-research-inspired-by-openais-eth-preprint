import VisitRuntimeCosts
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds

open Filter
open scoped Topology BigOperators

namespace Reconstruction.VisitRuntime

noncomputable section

/-- The exact rank premise of Corollary 2, equation (5). -/
def CorollaryTwoEstimate {Q : ℕ} (m : Fin Q → ℕ) (n R : ℕ) (β G : ℝ) : Prop :=
  β*(n:ℝ)/(48*Real.sqrt (2*G)) ≤
    (∑ t, (m t:ℝ))/(Q:ℝ) + (n:ℝ)*(R:ℝ)/(2*(Q:ℝ))

/-- The exact selected-node count and average rank premise of Corollary 5, equation (10). -/
def CorollaryFiveEstimate {Q : ℕ} (m : Fin Q → ℕ) (n R : ℕ) (cβ Cβ : ℝ) : Prop :=
  ∀ S : Finset (Fin Q), S.card = ⌈Cβ*((R:ℝ)+1)^2⌉₊ →
    cβ*(n:ℝ)/((R:ℝ)+1) ≤ (∑ t ∈ S, (m t:ℝ))/(S.card:ℝ)

/-- Finite costs derived from `Visits`. These are inputs to the numerical lemmas. -/
structure VisitBounds (N Q r R d₀ T : ℕ) (m : Fin Q → ℕ) : Prop where
  nodes_pos : 0 < Q
  groups_pos : 0 < r
  rank_pow : ∀ t, 2^(m t) ≤ T
  taylor_pow : ∀ s ≤ taylorCutoff N Q R d₀, 2^s ≤ T
  taylor_choose : ∀ s ≤ taylorCutoff N Q R d₀, N.choose s ≤ T
  largest : ∃ k : ℕ, N ≤ r*k ∧ 2^k ≤ T

theorem Visits.bounds {V F : Type*} [Fintype V] [DecidableEq V] {Q r R d₀ T : ℕ}
    {L : PhysicalLayout V F Q r R} (W : Visits L d₀ T) (U : Finset V) :
    VisitBounds (Fintype.card V) Q r R d₀ T (L.rankOn U) :=
  ⟨W.nodes_pos, W.groups_pos, W.rank_pow_le U, fun _ => W.taylor_pow_le,
    fun _ => W.taylor_choose_le,
    ⟨L.groupSize W.scanNode W.scanGroup, W.largest_size_ge, W.scan_pow_le⟩⟩

private theorem nat_top : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

private theorem log_top : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp nat_top

theorem log_of_pow_le {s T : ℕ} (h : 2^s ≤ T) : (s:ℝ)*Real.log 2 ≤ Real.log T := by
  simpa only [Real.log_pow] using Real.log_le_log (show 0 < (2:ℝ)^s by positivity)
    (show (2:ℝ)^s ≤ T by exact_mod_cast h)

theorem VisitBounds.log_largest {N Q r R d₀ T : ℕ} {m : Fin Q → ℕ}
    (B : VisitBounds N Q r R d₀ T m) : (N:ℝ)/(r:ℝ)*Real.log 2 ≤ Real.log T := by
  obtain ⟨k, hk, hT⟩ := B.largest
  have hr : 0 < (r:ℝ) := by exact_mod_cast B.groups_pos
  have hk' : (N:ℝ) ≤ (r:ℝ)*(k:ℝ) := by exact_mod_cast hk
  exact (mul_le_mul_of_nonneg_right ((div_le_iff₀' hr).mpr hk') (by positivity)).trans
    (log_of_pow_le hT)

theorem VisitBounds.averageRank_le {N Q r R d₀ T : ℕ} {m : Fin Q → ℕ}
    (B : VisitBounds N Q r R d₀ T m) (S : Finset (Fin Q)) (hS : 0 < S.card) :
    (∑ t ∈ S, (m t:ℝ))/(S.card:ℝ) ≤ Real.log T / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : 0 < (S.card:ℝ) := by exact_mod_cast hS
  apply (div_le_iff₀ hcard).mpr
  calc
    _ ≤ ∑ _ ∈ S, Real.log T / Real.log 2 := Finset.sum_le_sum (fun t _ =>
      (le_div_iff₀ hlog).mpr (log_of_pow_le (B.rank_pow t)))
    _ = _ := by simp [mul_comm]

private theorem floor_le_cutoff {N Q R d₀ : ℕ} {x : ℝ} (hQ : 0 < Q) (hx0 : 0 ≤ x) (hN : x ≤ N)
    (hx : x ≤ (d₀:ℝ)*(R:ℝ)/(Q:ℝ)) : ⌊x⌋₊ ≤ taylorCutoff N Q R d₀ := by
  have hQ' : 0 < (Q:ℝ) := by exact_mod_cast hQ
  refine le_min (Nat.floor_le_of_le hN) ((Nat.le_div_iff_mul_le hQ).mpr ?_)
  exact_mod_cast (show (⌊x⌋₊:ℝ)*(Q:ℝ) ≤ (d₀:ℝ)*(R:ℝ) from
    (mul_le_mul_of_nonneg_right (Nat.floor_le hx0) hQ'.le).trans ((le_div_iff₀ hQ').mp hx))

private theorem taylor_log_of_scale {N Q r R d₀ T : ℕ} {m : Fin Q → ℕ}
    (B : VisitBounds N Q r R d₀ T m) {x : ℝ} (h2 : 2 ≤ x) (hN : x ≤ N)
    (hx : x ≤ (d₀:ℝ)*(R:ℝ)/(Q:ℝ)) : (x/2)*Real.log 2 ≤ Real.log T := by
  have hr : x/2 ≤ (⌊x⌋₊:ℝ) := by linarith [Nat.lt_floor_add_one x]
  exact (mul_le_mul_of_nonneg_right hr (by positivity)).trans
    (log_of_pow_le (B.taylor_pow _ (floor_le_cutoff B.nodes_pos (by linarith) hN hx)))

def arbitraryNodeScale (N : ℕ) : ℝ := (N:ℝ)^(2/3:ℝ)

/-- Numerical part of Theorem 3. The first disjunct is a large scanned group,
and the second is the exact Corollary 2 bound at a suitable group size. -/
theorem theorem3_numerical {β c₀ ρ : ℝ} (hβ : 0 < β) (hc₀ : 0 < c₀) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (n Q r R d₀ T : ℕ) (m : Fin Q → ℕ), VisitBounds N Q r R d₀ T m →
      ρ*(N:ℝ) ≤ n → c₀*(N:ℝ) ≤ d₀ →
      (arbitraryNodeScale N / 2 * Real.log 2 ≤ Real.log T ∨
        ∃ G : ℝ, 0 < G ∧ G ≤ arbitraryNodeScale N ∧ CorollaryTwoEstimate m n R β G) →
      C*arbitraryNodeScale N ≤ Real.log T := by
  let a := β/(48*Real.sqrt 2)
  let k := min 1 (c₀*a)
  let C := Real.log 2 * min (1/2) (min (ρ*a/2) (k/2))
  have ha : 0 < a := by dsimp [a]; positivity
  have hk : 0 < k := lt_min zero_lt_one (mul_pos hc₀ ha)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmin : 0 < min (1/2:ℝ) (min (ρ*a/2) (k/2)) :=
    lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hpTop : Tendsto arbitraryNodeScale atTop atTop :=
    (tendsto_rpow_atTop (show (0:ℝ) < 2/3 by norm_num)).comp nat_top
  refine ⟨C, mul_pos hlog hmin, ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ), (hpTop.const_mul_atTop hk).eventually_ge_atTop 2]
    with N hN hbig n Q r R d₀ T m B hn hd hcases
  let p := arbitraryNodeScale N
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hN0 : 0 < (N:ℝ) := by linarith
  have hp : 0 < p := Real.rpow_pos_of_pos hN0 _
  have hpN : p ≤ N := by
    exact (Real.rpow_le_rpow_of_exponent_le hN1 (show (2/3:ℝ) ≤ 1 by norm_num)).trans_eq (Real.rpow_one _)
  have hroot := Real.sqrt_pos.mpr hp
  have hproduct : p * Real.sqrt p = N := by
    unfold p arbitraryNodeScale
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    norm_num
  have hratio : (N:ℝ)/Real.sqrt p = p := (div_eq_iff hroot.ne').mpr hproduct.symm
  have hC1 : C ≤ Real.log 2 * (1/2) := mul_le_mul_of_nonneg_left (min_le_left ..) hlog.le
  have hC2 : C ≤ Real.log 2 * (ρ*a/2) := mul_le_mul_of_nonneg_left
    ((min_le_right ..).trans (min_le_left ..)) hlog.le
  have hC3 : C ≤ Real.log 2 * (k/2) := mul_le_mul_of_nonneg_left
    ((min_le_right ..).trans (min_le_right ..)) hlog.le
  rcases hcases with hscan | ⟨G, hG, hGp, hh⟩
  · exact (mul_le_mul_of_nonneg_right hC1 hp.le).trans (by convert hscan using 1; ring)
  have hQ : 0 < (Q:ℝ) := by exact_mod_cast B.nodes_pos
  by_cases hR : (R:ℝ)/(Q:ℝ) ≤ a/Real.sqrt p
  · have hG' : a*(n:ℝ)/Real.sqrt p ≤ β*(n:ℝ)/(48*Real.sqrt (2*G)) := calc
      _ = β*(n:ℝ)/(48*Real.sqrt (2*p)) := by rw [Real.sqrt_mul (by norm_num)]; dsimp [a]; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num))
    have hR' : (n:ℝ)*(R:ℝ)/(2*(Q:ℝ)) ≤ a*(n:ℝ)/Real.sqrt p/2 := by
      convert mul_le_mul_of_nonneg_left hR (show 0 ≤ (n:ℝ)/2 by positivity) using 1 <;> ring
    have hmean := B.averageRank_le Finset.univ (by simpa using B.nodes_pos)
    rw [Finset.card_univ, Fintype.card_fin] at hmean
    have hbase : ((ρ*a/2)*p) ≤ a*(n:ℝ)/Real.sqrt p/2 := calc
      _ = a*(ρ*(N:ℝ))/Real.sqrt p/2 := by
        calc
          _ = (ρ*a/2)*((N:ℝ)/Real.sqrt p) := congrArg ((ρ*a/2)*·) hratio.symm
          _ = _ := by ring
      _ ≤ _ := by gcongr
    have hsmall : (ρ*a/2)*p ≤ Real.log T/Real.log 2 := by
      unfold CorollaryTwoEstimate at hh
      linarith only [hbase, hR', hmean, hG', hh]
    exact (mul_le_mul_of_nonneg_right hC2 hp.le).trans (by
      convert (le_div_iff₀ hlog).mp hsmall using 1; ring)
  · have hscale : k*p ≤ (d₀:ℝ)*(R:ℝ)/(Q:ℝ) := calc
      _ ≤ (c₀*a)*p := mul_le_mul_of_nonneg_right (min_le_right ..) hp.le
      _ = (c₀*(N:ℝ))*(a/Real.sqrt p) := by
        calc
          _ = (c₀*a)*((N:ℝ)/Real.sqrt p) := congrArg ((c₀*a)*·) hratio.symm
          _ = _ := by ring
      _ ≤ (d₀:ℝ)*((R:ℝ)/(Q:ℝ)) := mul_le_mul hd (le_of_not_ge hR) (by positivity) (by positivity)
      _ = _ := by ring
    have hkN : k*p ≤ (N:ℝ) := (mul_le_of_le_one_left hp.le (min_le_left ..)).trans hpN
    exact (mul_le_mul_of_nonneg_right hC3 hp.le).trans (by
      convert taylor_log_of_scale B hbig hkN hscale using 1; ring)

/-- Natural logarithmic scale per variable in Theorem 6. -/
def scheduledRate (N : ℕ) : ℝ := Real.log (Real.log N)/Real.sqrt (Real.log N)

private def nodeLog (q : ℝ) : ℝ := 1 + Real.log q

private def nodeRate (q : ℝ) : ℝ := Real.sqrt (nodeLog q)/Real.sqrt q

private theorem log_choose_of_visits {N Q r R d₀ T s : ℕ} {m : Fin Q → ℕ}
    (B : VisitBounds N Q r R d₀ T m) (hs : 0 < s) (hsN : 2*s ≤ N)
    (hsc : s ≤ taylorCutoff N Q R d₀) :
    (s:ℝ)*Real.log ((N:ℝ)/(2*(s:ℝ))) ≤ Real.log T := by
  have hs0 : 0 < (s:ℝ) := by exact_mod_cast hs
  have hN : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsn : s ≤ N+1 := by omega
  have h2s : 2*(s:ℝ) ≤ N := by exact_mod_cast hsN
  have hchoose : ((N:ℝ)/(2*(s:ℝ)))^s ≤ (N.choose s:ℝ) := calc
    _ = ((N:ℝ)/2)^s / (s:ℝ)^s := by rw [← div_div, div_pow]
    _ ≤ ((N+1-s : ℕ):ℝ)^s / (s:ℝ)^s :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity)
        (by push_cast [Nat.cast_sub hsn]; linarith) _) (by positivity)
    _ ≤ ((N+1-s : ℕ):ℝ)^s / (s.factorial:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast s.factorial_pos)
        (by exact_mod_cast s.factorial_le_pow)
    _ ≤ _ := by exact_mod_cast (Nat.pow_le_choose (α := ℝ) s N)
  simpa only [Real.log_pow] using Real.log_le_log (by positivity)
    (hchoose.trans (by exact_mod_cast B.taylor_choose s hsc))

private theorem large_node_work {N n Q r R d₀ T : ℕ} {m : Fin Q → ℕ}
    (B : VisitBounds N Q r R d₀ T m) {a c₀ ρ cβ Cβ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1/2) (hac : a ≤ c₀/2) (hρ : 0 < ρ)
    (hcβ : 0 < cβ) (hCβ : 0 < Cβ)
    (hn : ρ*(N:ℝ) ≤ n) (hd : c₀*(N:ℝ) ≤ d₀) (hR : 1 ≤ R)
    (hql : 1 ≤ Real.log Q) (hCq : Cβ ≤ nodeLog Q)
    (hbig : 2 ≤ a*(N:ℝ)/(Real.sqrt Q*Real.sqrt (nodeLog Q)))
    (hc5 : CorollaryFiveEstimate m n R cβ Cβ) :
    min (Real.log 2*cβ*ρ) (a/8) * ((N:ℝ)*nodeRate Q) ≤ Real.log T := by
  let q : ℝ := Q
  let v := Real.sqrt q
  let w := Real.sqrt (nodeLog q)
  let u := v/w
  have hQ : 0 < q := by dsimp [q]; exact_mod_cast B.nodes_pos
  have hQ1 : 1 ≤ q := by dsimp [q]; exact_mod_cast B.nodes_pos
  have hL : 1 ≤ nodeLog q := by unfold nodeLog; linarith
  have hv : 0 < v := Real.sqrt_pos.mpr hQ
  have hw : 0 < w := Real.sqrt_pos.mpr (by linarith)
  have hu : 0 < u := div_pos hv hw
  have hv2 : v^2 = q := Real.sq_sqrt hQ.le
  have hw2 : w^2 = nodeLog q := Real.sq_sqrt (by linarith)
  have hvr : 1 ≤ v := Real.one_le_sqrt.mpr hQ1
  have hwr : 1 ≤ w := Real.one_le_sqrt.mpr hL
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have htarget : 0 ≤ (N:ℝ)*nodeRate q := mul_nonneg hN0 (div_nonneg hw.le hv.le)
  have href : (R:ℝ)+1 ≤ 2*(R:ℝ) := by exact_mod_cast (show R+1 ≤ 2*R by omega)
  by_cases hsmall : (R:ℝ)+1 ≤ u
  · let k := ⌈Cβ*((R:ℝ)+1)^2⌉₊
    have hkp : 0 < k := Nat.ceil_pos.mpr (mul_pos hCβ (by positivity))
    have hkle : k ≤ Q := by
      apply Nat.ceil_le.mpr
      calc
        _ ≤ Cβ*u^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsmall 2) hCβ.le
        _ = (Cβ/nodeLog q)*q := by unfold u; rw [div_pow, hv2, hw2]; ring
        _ ≤ _ := mul_le_of_le_one_left hQ.le ((div_le_one (by linarith : 0 < nodeLog q)).mpr hCq)
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin Q)))
      (by simpa using hkle)
    have hrank := (hc5 S hS).trans (B.averageRank_le S (hS.symm ▸ hkp))
    have hcoef : cβ*ρ*((N:ℝ)*nodeRate q) ≤ cβ*(n:ℝ)/((R:ℝ)+1) := calc
      _ = cβ*(ρ*(N:ℝ))/u := by
        change cβ*ρ*((N:ℝ)*(w/v)) = cβ*(ρ*(N:ℝ))/(v/w)
        field_simp
      _ ≤ _ := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hn hcβ.le) (by positivity) hsmall
    exact (mul_le_mul_of_nonneg_right (min_le_left ..) htarget).trans (by
      convert (le_div_iff₀ (Real.log_pos (by norm_num))).mp (hcoef.trans hrank) using 1; ring)
  · let x := a*(N:ℝ)/(v*w)
    let s := ⌊x⌋₊
    have hx2 : 2 ≤ x := hbig
    have hx0 : 0 ≤ x := by linarith
    have hxN : x ≤ (N:ℝ)/2 := calc
      _ ≤ a*(N:ℝ) := div_le_self (by positivity)
        ((one_mul (1:ℝ)).symm.le.trans (mul_le_mul hvr hwr zero_le_one hv.le))
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right ha1 hN0]
    have hsc : s ≤ taylorCutoff N Q R d₀ := by
      apply floor_le_cutoff B.nodes_pos hx0 (hxN.trans (by linarith))
      calc
        _ = a*(N:ℝ)*u/q := by unfold x u; field_simp; nlinarith only [hv2]
        _ ≤ (c₀*(N:ℝ))*(R:ℝ)/q := by
          apply div_le_div_of_nonneg_right _ hQ.le
          have h1 : a*(N:ℝ) ≤ c₀*(N:ℝ)/2 := by linarith only [mul_le_mul_of_nonneg_right hac hN0]
          have h2 : u ≤ 2*(R:ℝ) := (le_of_not_ge hsmall).trans href
          calc
            _ ≤ (c₀*(N:ℝ)/2)*(2*(R:ℝ)) := mul_le_mul h1 h2 hu.le ((mul_nonneg ha.le hN0).trans h1)
            _ = _ := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)) hQ.le
    have hslo : x/2 ≤ (s:ℝ) := by linarith [Nat.lt_floor_add_one x]
    have hshi : (s:ℝ) ≤ x := Nat.floor_le hx0
    have hs : 0 < s := by exact_mod_cast (show 0 < (s:ℝ) by linarith)
    have hsN : 2*s ≤ N := by exact_mod_cast (show 2*(s:ℝ) ≤ N by linarith)
    have hvle : v ≤ (N:ℝ)/(2*(s:ℝ)) := by
      have hs0 : 0 < (s:ℝ) := by exact_mod_cast hs
      apply (le_div_iff₀ (by positivity)).mpr
      calc
        _ ≤ v*(2*x) := by gcongr
        _ = (2*a*(N:ℝ))/w := by unfold x; field_simp
        _ ≤ 2*a*(N:ℝ) := div_le_self (by positivity) hwr
        _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right ha1 hN0]
    have hlog := Real.log_le_log hv hvle
    change Real.log (Real.sqrt q) ≤ _ at hlog
    rw [Real.log_sqrt hQ.le] at hlog
    have hlog' : nodeLog q/4 ≤ Real.log ((N:ℝ)/(2*(s:ℝ))) := by
      unfold nodeLog
      linarith only [hql, hlog]
    have henergy : (a/8)*((N:ℝ)*nodeRate q) ≤ Real.log T := calc
      _ = (x/2)*(nodeLog q/4) := by
        unfold x nodeRate
        change _ * (_ * (w/v)) = _
        rw [← hw2]
        field_simp
        ring
      _ ≤ (s:ℝ)*Real.log ((N:ℝ)/(2*(s:ℝ))) := mul_le_mul hslo hlog' (by positivity) (by positivity)
      _ ≤ _ := log_choose_of_visits B hs hsN hsc
    exact (mul_le_mul_of_nonneg_right (min_le_right ..) htarget).trans henergy

private theorem logpow_eventually (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, (Real.log x)^k ≤ x^d := by
  have hh := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hd).bound (show (0:ℝ) < 1 by norm_num)
  filter_upwards [hh, eventually_ge_atTop (1:ℝ)] with x h hx
  change ‖(Real.log x)^(k:ℝ)‖ ≤ 1*‖x^d‖ at h
  have hx0 : 0 ≤ x := by linarith
  simpa only [one_mul, Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg hx) _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)] using h

private theorem nodeRate_comparison {x q K : ℝ} (hx : 0 < x) (hq : 1 ≤ q) (hK : 1 ≤ K)
    (hy : 1 ≤ Real.log x) (hsq : (Real.log x)^2 ≤ Real.sqrt x)
    (hcap : q ≤ K*x/Real.log x) :
    (Real.log x/Real.sqrt x)/(2*K) ≤ nodeRate q := by
  have hq0 : 0 < q := by linarith
  have hK0 : 0 < K := by linarith
  have hy0 : 0 < Real.log x := by linarith
  have hv := Real.sqrt_pos.mpr hx
  have hL : 1 ≤ nodeLog q := by unfold nodeLog; linarith [Real.log_nonneg hq]
  have hz : 0 ≤ nodeLog q/q := div_nonneg (by linarith) hq0.le
  have hbase : (Real.log x/Real.sqrt x)^2 ≤ (2*K)*(nodeLog q/q) := by
    rw [div_pow, Real.sq_sqrt hx.le]
    by_cases h : q ≤ Real.sqrt x
    · calc
        _ ≤ 1/Real.sqrt x := by
          apply (div_le_iff₀ hx).mpr
          have he : 1/Real.sqrt x*x = Real.sqrt x := by field_simp; exact (Real.sq_sqrt hx.le).symm
          rwa [he]
        _ ≤ 1/q := one_div_le_one_div_of_le hq0 h
        _ ≤ nodeLog q/q := div_le_div_of_nonneg_right hL hq0.le
        _ ≤ _ := le_mul_of_one_le_left hz (by linarith)
    · have hqlog := Real.log_le_log hv (le_of_not_ge h)
      rw [Real.log_sqrt hx.le] at hqlog
      have h1 := mul_le_mul_of_nonneg_right ((le_div_iff₀ hy0).mp hcap) hy0.le
      have h2 := mul_le_mul_of_nonneg_left (show Real.log x/2 ≤ nodeLog q by unfold nodeLog; linarith)
        (mul_nonneg hK0.le hx.le)
      rw [← mul_div_assoc]
      exact (div_le_div_iff₀ hx hq0).mpr (by nlinarith only [h1, h2])
  unfold nodeRate
  rw [← Real.sqrt_div (by linarith : 0 ≤ nodeLog q)]
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hz, div_pow]
  calc
    _ ≤ ((2*K)*(nodeLog q/q))/(2*K)^2 := div_le_div_of_nonneg_right hbase (sq_nonneg _)
    _ = (nodeLog q/q)/(2*K) := by field_simp
    _ ≤ _ := div_le_self hz (by linarith)

/-- Numerical part of Theorem 6. The rank premises are the exact Corollary 5
estimate and the coordinate-rank consequence of constant rows. -/
theorem theorem6_numerical {A c₀ ρ β cβ Cβ : ℝ}
    (hA : 0 < A) (hc₀ : 0 < c₀) (hρ : 0 < ρ) (hβ : 0 < β)
    (hcβ : 0 < cβ) (hCβ : 0 < Cβ) (r₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (n Q r R d₀ T : ℕ) (m : Fin Q → ℕ), VisitBounds N Q r R d₀ T m →
      ρ*(N:ℝ) ≤ n → c₀*(N:ℝ) ≤ d₀ → (r:ℝ)^(2*Q) ≤ (N:ℝ)^A →
      (r₀ ≤ r → CorollaryFiveEstimate m n R cβ Cβ) →
      (r₀ ≤ r → R = 0 → ∀ t, β*(n:ℝ) ≤ m t) →
      C*((N:ℝ)*scheduledRate N) ≤ Real.log T := by
  let K := 1+3*A/2
  let a := min (1/2) (c₀/2)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hK0 : 0 < K := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp (log_top.eventually_ge_atTop (max 1 Cβ))
  let b := min 1 (c₀/((Q₀:ℝ)+1))
  let Cbig := min (Real.log 2*cβ*ρ) (a/8)
  let C := min (Real.log 2) (min (β*ρ*Real.log 2) (min (b/2*Real.log 2) (Cbig/(2*K))))
  have hb : 0 < b := lt_min zero_lt_one (by positivity)
  have hCbig : 0 < Cbig := lt_min (by positivity) (by positivity)
  have hC : 0 < C := lt_min hlog2 (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hC1 : C ≤ Real.log 2 := min_le_left ..
  have hC2 : C ≤ β*ρ*Real.log 2 := (min_le_right ..).trans (min_le_left ..)
  have hC3 : C ≤ b/2*Real.log 2 := (min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))
  have hC4 : C ≤ Cbig/(2*K) := (min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..))
  have hlogdiv := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp nat_top).eventually
    (Iio_mem_nhds (show 0 < a/(2*K) by positivity))
  have hrTop := (tendsto_rpow_atTop (show (0:ℝ) < 1/3 by norm_num)).comp log_top
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℕ), (Real.tendsto_log_atTop.comp log_top).eventually_ge_atTop 1,
    log_top.eventually (logpow_eventually 2 (show (0:ℝ) < 1/2 by norm_num)),
    log_top.eventually (logpow_eventually 1 (show (0:ℝ) < 1/6 by norm_num)),
    hlogdiv, hrTop.eventually_ge_atTop (r₀:ℝ), (nat_top.const_mul_atTop hb).eventually_ge_atTop 2]
    with N hN hy hy2 hy1 hdiv hr₀ hbN n Q r R d₀ T m B hn hd hsize hc5 hzero
  let x := Real.log N
  let y := Real.log x
  change 1 ≤ y at hy
  change x/(N:ℝ) < a/(2*K) at hdiv
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hx : 0 < x := Real.log_pos (by exact_mod_cast hN)
  have hy0 : 0 < y := by linarith
  have hr : 0 < (r:ℝ) := by exact_mod_cast B.groups_pos
  have hq : 0 < (Q:ℝ) := by exact_mod_cast B.nodes_pos
  have hroot := Real.sqrt_pos.mpr hx
  have hy2' : y^2 ≤ Real.sqrt x := by simpa only [Real.sqrt_eq_rpow] using hy2
  have hrate : 0 ≤ scheduledRate N := div_nonneg hy0.le hroot.le
  have hrate1 : scheduledRate N ≤ 1 := (div_le_one hroot).mpr
    (show y ≤ Real.sqrt x by nlinarith only [hy2', mul_le_mul_of_nonneg_right hy hy0.le])
  have hbase : 0 ≤ (N:ℝ)*scheduledRate N := mul_nonneg hN0.le hrate
  by_cases hrg : (r:ℝ) ≤ Real.sqrt x/y
  · have hg : scheduledRate N ≤ 1/(r:ℝ) := by
      change y/Real.sqrt x ≤ _
      exact (div_le_div_iff₀ hroot hr).mpr (by linarith only [(le_div_iff₀ hy0).mp hrg])
    exact (mul_le_mul_of_nonneg_right hC1 hbase).trans (by
      calc
        _ ≤ Real.log 2*((N:ℝ)*(1/(r:ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hN0.le) hlog2.le
        _ ≤ _ := by convert B.log_largest using 1; ring)
  have hpow : x^(1/3:ℝ)*x^(1/6:ℝ) = Real.sqrt x := by
    rw [← Real.rpow_add hx, Real.sqrt_eq_rpow]; congr 1; norm_num
  have hrg' : x^(1/3:ℝ) ≤ (r:ℝ) := le_of_lt (calc
    _ ≤ Real.sqrt x/y := (le_div_iff₀ hy0).mpr
      ((mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hy1) (Real.rpow_nonneg hx.le _)).trans_eq hpow)
    _ < _ := lt_of_not_ge hrg)
  have hrmin : r₀ ≤ r := by exact_mod_cast (hr₀.trans hrg')
  have hlogr := Real.log_le_log (Real.rpow_pos_of_pos hx (1/3:ℝ)) hrg'
  rw [Real.log_rpow hx] at hlogr
  have hlogD := Real.log_le_log (show 0 < (r:ℝ)^(2*Q) by positivity) hsize
  rw [Real.log_pow, Real.log_rpow hN0] at hlogD
  push_cast at hlogD
  have hqcap : (Q:ℝ) ≤ K*x/y := by
    apply (le_div_iff₀ hy0).mpr
    have hh := (mul_le_mul_of_nonneg_left hlogr (show 0 ≤ 2*(Q:ℝ) by positivity)).trans hlogD
    have hk : 3*A/2 ≤ K := by dsimp [K]; linarith
    nlinarith only [hh, mul_le_mul_of_nonneg_right hk hx.le]
  have hNr : (N:ℝ)*scheduledRate N ≤ N := mul_le_of_le_one_right hN0.le hrate1
  by_cases hR : R = 0
  · let t : Fin Q := ⟨0, B.nodes_pos⟩
    have hh := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hn hβ.le).trans
      (hzero hrmin hR t)) hlog2.le
    exact (mul_le_mul_of_nonneg_right hC2 hbase).trans ((mul_le_mul_of_nonneg_left hNr (by positivity)).trans
      (by convert hh.trans (log_of_pow_le (B.rank_pow t)) using 1; ring))
  have hR1 : 1 ≤ R := by omega
  by_cases hQlt : Q < Q₀
  · have hsmall : (Q:ℝ) ≤ (Q₀:ℝ)+1 := by exact_mod_cast (show Q ≤ Q₀+1 by omega)
    have hcut : b*(N:ℝ) ≤ (d₀:ℝ)*(R:ℝ)/(Q:ℝ) := by
      apply (le_div_iff₀ hq).mpr
      have hb' : b*((Q₀:ℝ)+1) ≤ c₀ := (le_div_iff₀ (by positivity)).mp (min_le_right ..)
      have hmul := (mul_le_mul_of_nonneg_left hsmall hb.le).trans hb'
      calc
        _ = (b*(Q:ℝ))*(N:ℝ) := by ring
        _ ≤ (d₀:ℝ) := (mul_le_mul_of_nonneg_right hmul hN0.le).trans hd
        _ ≤ _ := le_mul_of_one_le_right (Nat.cast_nonneg _) (by exact_mod_cast hR1)
    have hNb : b*(N:ℝ) ≤ N := mul_le_of_le_one_left hN0.le (min_le_left ..)
    exact (mul_le_mul_of_nonneg_right hC3 hbase).trans ((mul_le_mul_of_nonneg_left hNr (by positivity)).trans
      (by convert taylor_log_of_scale B hbN hNb hcut using 1; ring))
  have hlq : max 1 Cβ ≤ Real.log Q := hQ₀ Q (by omega)
  have hqlog : 1 ≤ Real.log Q := (le_max_left ..).trans hlq
  have hqlogβ : Cβ ≤ nodeLog Q := (le_max_right ..).trans (by unfold nodeLog; linarith)
  have hnodelog : nodeLog Q ≤ Q := by unfold nodeLog; linarith [Real.log_le_sub_one_of_pos hq]
  have hnodelog0 : 0 < nodeLog Q := by unfold nodeLog; linarith
  have hprod : Real.sqrt Q*Real.sqrt (nodeLog Q) ≤ K*x := calc
    _ ≤ Real.sqrt Q*Real.sqrt Q := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnodelog) (by positivity)
    _ = Q := Real.mul_self_sqrt hq.le
    _ ≤ K*x := hqcap.trans (div_le_self (by positivity) hy)
  have hfloor : 2 ≤ a*(N:ℝ)/(Real.sqrt Q*Real.sqrt (nodeLog Q)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh : x < (a*(N:ℝ))/(2*K) := by
      rw [mul_div_right_comm]
      exact (div_lt_iff₀ hN0).mp hdiv
    have hh' := (lt_div_iff₀ (by positivity : 0 < 2*K)).mp hh
    nlinarith only [mul_le_mul_of_nonneg_left hprod (show (0:ℝ) ≤ 2 by norm_num), hh']
  have hcmp := nodeRate_comparison hx (by exact_mod_cast B.nodes_pos) hK hy hy2' hqcap
  have hh := large_node_work B ha (min_le_left ..) (min_le_right ..) hρ hcβ hCβ hn hd hR1 hqlog hqlogβ
    hfloor (hc5 hrmin)
  apply (mul_le_mul_of_nonneg_right hC4 hbase).trans
  calc
    _ = Cbig * ((N:ℝ)*((y/Real.sqrt x)/(2*K))) := by unfold scheduledRate; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmp hN0.le) hCbig.le).trans hh

end

end Reconstruction.VisitRuntime
