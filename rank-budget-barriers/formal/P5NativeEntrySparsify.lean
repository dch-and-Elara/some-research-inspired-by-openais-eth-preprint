import P5NativeEntryTuning

/-! The root preliminary tuning and, for the actual signed-unit input
entered as a 2-CNF, the source's exact least successful power of two in
its independent sparsifier parameter search (source lines 3841–3863). -/
namespace Paper5.NativeEntry
open Real Filter
open scoped Topology

theorem printedGroups_literal {n : ℕ} (h : 0<sourceNu n) :
    printedGroups n=⌊sqrt (sourceLambda n:ℝ)/(sourceNu n:ℝ)^2⌋₊ := by
  let a := sourceLambda n
  let b := (sourceNu n)^2
  let r := printedGroups n
  have hb : 0<b := pow_pos h _
  have hbR : 0<(b:ℝ) := by exact_mod_cast hb
  have hBcast : (sourceNu n:ℝ)^2=(b:ℝ) := by simp [b]
  rw [hBcast]
  apply Eq.symm
  change ⌊sqrt (a:ℝ)/(b:ℝ)⌋₊=r
  apply (Nat.floor_eq_iff (div_nonneg (sqrt_nonneg _) hbR.le)).2
  constructor
  · apply (le_div_iff₀ hbR).mpr
    simpa [a,b,r] using (printed_r_times_nu_le (n:=n))
  · apply (div_lt_iff₀ hbR).mpr
    have hs : sqrt (a:ℝ)<(a.sqrt:ℝ)+1 := by
      apply (sq_lt_sq₀ (sqrt_nonneg _) (by positivity)).mp
      rw [sq_sqrt (by positivity)]
      exact_mod_cast Nat.lt_succ_sqrt' a
    have hr : a.sqrt<(r+1)*b := (Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_self _)
    exact hs.trans_le (by exact_mod_cast Nat.succ_le_of_lt hr)

theorem ceilSqrt_literal (a : ℕ) : ceilSqrt a=⌈sqrt (a:ℝ)⌉₊ := by
  have hs : sqrt (a:ℝ)≤(ceilSqrt a:ℝ) := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (by positivity)]
    exact_mod_cast ceilSqrt_sq_ge a
  refine le_antisymm ?_ (Nat.ceil_le.mpr hs)
  unfold ceilSqrt
  split_ifs with h
  · have he : (a.sqrt:ℝ)=sqrt (a:ℝ) := by
      apply (sq_eq_sq₀ (by positivity) (sqrt_nonneg _)).mp
      rw [sq_sqrt (by positivity)]
      exact_mod_cast h
    exact_mod_cast (show (a.sqrt:ℝ)≤(⌈sqrt (a:ℝ)⌉₊:ℝ) from he.le.trans (Nat.le_ceil _))
  · have hl : (a.sqrt:ℝ)<sqrt (a:ℝ) := by
      apply (sq_lt_sq₀ (by positivity) (sqrt_nonneg _)).mp
      rw [sq_sqrt (by positivity)]
      exact_mod_cast lt_of_le_of_ne (Nat.sqrt_le' a) h
    exact Nat.succ_le_of_lt (by exact_mod_cast hl.trans_le (Nat.le_ceil _))

private theorem quarticStep {j : ℕ} (h : 16≤j) : (j+1)^4≤2*j^4 := by
  have h0 : 16*(j+1)≤17*j := by omega
  have hh := Nat.pow_le_pow_left h0 4
  simp only [mul_pow] at hh
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0<(16:ℕ)^4)
  calc
    _ ≤ 17^4*j^4 := hh
    _ ≤ _ := by rw [←mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)

private theorem quarticEventually (j : ℕ) (h : 32≤j) : 4*j^4≤2^(j-1) := by
  induction j,h using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    have hh := quarticStep (j:=j) (by omega)
    calc
      _ ≤ 4*(2*j^4) := Nat.mul_le_mul_left 4 hh
      _ = 2*(4*j^4) := by ring
      _ ≤ 2*2^(j-1) := Nat.mul_le_mul_left 2 ih
      _ = _ := by rw [show j+1-1=(j-1)+1 by omega,pow_succ']

theorem eventual_prelim_guard : ∃ n₀ : ℕ, ∀ n≥n₀,2≤printedGroups n := by
  have hL : Tendsto sourceLambda atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop ((2:ℕ)^k)] with n hn
    have h := Nat.clog_mono_right 2 hn
    simpa only [Nat.clog_pow 2 _ (by decide),sourceLambda] using h
  have hN' : Tendsto sourceNu atTop atTop := hL.comp hL
  obtain ⟨n₀,hcut⟩ := eventually_atTop.mp (hN'.eventually (eventually_ge_atTop 32))
  refine ⟨n₀,?_⟩
  intro n hn
  have hN : 32≤sourceNu n := hcut n hn
  have hLam : (2:ℕ)^(sourceNu n-1)<sourceLambda n :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mp (by
      change sourceNu n-1<sourceNu n
      omega)
  have hSq : 4*(sourceNu n)^4≤sourceLambda n :=
    (quarticEventually _ hN).trans hLam.le
  unfold printedGroups
  apply (Nat.le_div_iff_mul_le (pow_pos (by omega : 0<sourceNu n) _)).mpr
  apply Nat.le_sqrt'.mpr
  calc
    _ = 4*(sourceNu n)^4 := by ring
    _ ≤ _ := hSq

def sparOK (s j : ℕ) : Prop := 2≤j ∧ 4*(4+j)*s≤2^j

instance decSparOK (s j : ℕ) : Decidable (sparOK s j) := by
  unfold sparOK
  infer_instance

theorem spar_log_linear (a : ℕ) (ha : 1≤a) : 2*a+9≤8*(2:ℕ)^a := by
  induction a,ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    calc
      _ ≤ 2*(2*a+9) := by omega
      _ ≤ 2*(8*2^a) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ']; ring

theorem spar_ok_test (s : ℕ) (hs : 2≤s) : sparOK s (2*sourceLambda s+5) := by
  let a := sourceLambda s
  have ha : 1≤a := lambda_pos hs
  refine ⟨by omega,?_⟩
  change 4*(4+(2*a+5))*s≤2^(2*a+5)
  calc
    _ = 4*((2*a+9)*s) := by ring
    _ ≤ 4*((8*2^a)*2^a) := Nat.mul_le_mul_left _
      (Nat.mul_le_mul (spar_log_linear a ha) (Nat.le_pow_clog (by decide) s))
    _ = _ := by
      rw [pow_add,show 2*a=a+a by omega,pow_add]
      ring

def sparExponent (s : ℕ) (hs : 2≤s) : ℕ :=
  Nat.find ⟨_,spar_ok_test s hs⟩

def sparB₂ (s : ℕ) (hs : 2≤s) : ℕ := 2*(1+2^(sparExponent s hs))

theorem spar_first_success (s : ℕ) (hs : 2≤s) :
    sparOK s (sparExponent s hs) ∧ ∀ j<sparExponent s hs,¬sparOK s j := by
  exact ⟨Nat.find_spec _,fun _ hj=>Nat.find_min _ hj⟩

theorem spar_exact_guard (s j : ℕ) :
    sparOK s j ↔ 4≤2^j ∧ 4*Nat.clog 2 (4*4*2^j)*s≤2^j := by
  have he : 4*4*(2:ℕ)^j=(2:ℕ)^(4+j) := by rw [pow_add]; rfl
  rw [he,Nat.clog_pow 2 _ (by decide)]
  have hh : (4:ℕ)≤2^j ↔ 2≤j := by
    change (2:ℕ)^2≤2^j ↔ 2≤j
    exact Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))
  rw [hh]
  rfl

theorem spar_b_le (s : ℕ) (hs : 2≤s) : sparB₂ s hs≤258*s^2 := by
  let a := sourceLambda s
  have hpos : 0<a := lambda_pos hs
  have hS : (2:ℕ)^a≤2*s := by
    have he : (2:ℕ)^(a-1)<s := (Nat.lt_clog_iff_pow_lt (by decide)).mp
      (by change a-1<a; omega)
    have hea : a=(a-1)+1 := by omega
    conv_lhs => rw [hea,pow_succ']
    exact Nat.mul_le_mul_left _ he.le
  have hp : sparExponent s hs≤2*a+5 := Nat.find_min' _ (spar_ok_test s hs)
  have hpow : (2:ℕ)^(sparExponent s hs)≤128*s^2 := by
    calc
      _ ≤ (2:ℕ)^(2*a+5) := Nat.pow_le_pow_right (by decide) hp
      _ = 32*((2:ℕ)^a)^2 := by rw [pow_add,Nat.mul_comm 2 a,pow_mul]; ring
      _ ≤ 32*(2*s)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS 2)
      _ = _ := by ring
  have hn : 1≤s^2 := Nat.succ_le_of_lt (pow_pos (by omega) _)
  unfold sparB₂
  omega

theorem literal_unit_source_B_bound {n : ℕ} (h : 2≤printedGroups n) :
    0<sparB₂ (printedGroups n) h ∧ sparB₂ (printedGroups n) h≤258*sourceLambda n := by
  refine ⟨by unfold sparB₂; positivity,?_⟩
  have hs : printedGroups n≤(sourceLambda n).sqrt := Nat.div_le_self _ _
  exact (spar_b_le (printedGroups n) h).trans (Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left hs 2).trans (Nat.sqrt_le' _)))

#print axioms printedGroups_literal
#print axioms ceilSqrt_literal
#print axioms eventual_prelim_guard
#print axioms spar_ok_test
#print axioms spar_first_success
#print axioms spar_exact_guard
#print axioms spar_b_le
#print axioms literal_unit_source_B_bound
end Paper5.NativeEntry