import P5HybridClosurePrintedGrowth

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000

/-! (H=ceil( s/floor(sqrt({ceil(log2( s)}))) at the
same four-clone source count (s). All integer operations are retained. -/
namespace V8NativeMessage.N2DPost
open Filter Real Paper5.HybridClosure.Printed J9PrintedSchedule
open scoped Topology

noncomputable section

def threshold (N : ℕ) : ℕ := leafThreshold (dSize N) (dLambda N)

def rate (N : ℕ) : ℝ := (N:ℝ)/sqrt (log (N:ℝ))

def dCoeff : ℝ := 1/(32*sqrt printedLogConst)

theorem dCoeff_pos : 0 < dCoeff := by
  unfold dCoeff
  have hc := printed_log_const_pos
  positivity

theorem d_size_literal_nat (N : ℕ) : dSize N=21*N/2 := by
  unfold dSize
  omega

theorem d_size_literal_cubic {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (W×W)) (cubic : ∀ v,GraphCutMoments.degree F v=3) (σ : W→Bool) :
    ((Fintype.card (Paper5.HybridClosure.Clone W)+
       (MainClonedCNF.formula F (MainClonedCNF.leftSlot F cubic)
         (MainClonedCNF.rightSlot F cubic) σ).length:ℕ):ℝ) =
      21*(Fintype.card W:ℝ)/2 := by
  rw [d_size_is_cloned F cubic σ]
  have h := GraphCutMoments.regular_edge_count F 3 cubic
  have hs : 2*dSize (Fintype.card W)=21*Fintype.card W := by
    unfold dSize
    omega
  have hs' : 2*(dSize (Fintype.card W):ℝ)=21*(Fintype.card W:ℝ) := by exact_mod_cast hs
  linarith only [hs']

theorem d_lambda_log_bound (N : ℕ) (hN : 2≤N) :
    (dLambda N:ℝ)≤printedLogConst*log (N:ℝ) := by
  have hS : dSize N≤N^5 := by
    refine (d_size_bounds N).2.trans ?_
    have hp : 11≤N^4 := (by decide : (11:ℕ)≤2^4).trans (Nat.pow_le_pow_left hN 4)
    exact (Nat.mul_le_mul_right _ hp).trans_eq (pow_succ _ _).symm
  have hs : 1≤dSize N := (by omega : 1≤N).trans (d_size_bounds N).1
  simpa [dLambda,printedLogConst] using clog_real_log_bound N (dSize N) 5 hN hs hS

theorem d_threshold_log_bound (N : ℕ) (hN : 2≤N) :
    dCoeff*rate N≤(threshold N:ℝ)/32 := by
  let s := dSize N
  let lam := dLambda N
  let H := threshold N
  have hS : 2≤s := hN.trans (d_size_bounds N).1
  have hlog : 0<log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  have hLam : 0<lam := by
    change 0<Nat.clog 2 s
    apply (Nat.lt_clog_iff_pow_lt (by decide)).mpr
    simp
    omega
  have hd : 0<lam.sqrt := Nat.sqrt_pos.2 hLam
  have hRound : s≤H*lam.sqrt := le_roundup_mul s lam.sqrt hd
  have hNh : (N:ℝ)≤(H:ℝ)*(lam.sqrt:ℝ) := by
    have h := (d_size_bounds N).1.trans hRound
    exact_mod_cast h
  have hSqrt : (lam.sqrt:ℝ)≤sqrt printedLogConst*sqrt (log (N:ℝ)) :=
    ((sqrt_nat_le_real lam).trans (sqrt_le_sqrt (d_lambda_log_bound N hN))).trans_eq
      (sqrt_mul printed_log_const_pos.le _)
  have hFin : (N:ℝ)≤(H:ℝ)*(sqrt printedLogConst*sqrt (log (N:ℝ))) :=
    hNh.trans (mul_le_mul_of_nonneg_left hSqrt (by positivity))
  have hDiv : (N:ℝ)/(sqrt printedLogConst*sqrt (log (N:ℝ)))≤(H:ℝ) :=
    (div_le_iff₀ (mul_pos (sqrt_pos.2 printed_log_const_pos) (sqrt_pos.2 hlog))).2
      (by simpa only [mul_comm] using hFin)
  calc
    _ = ((N:ℝ)/(sqrt printedLogConst*sqrt (log (N:ℝ))))/32 := by
      unfold dCoeff rate
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hDiv (by norm_num)

theorem source_root_eventually_above_cutoff :
    ∀ᶠ N : ℕ in atTop,threshold N<24*N :=
  d_printed_eventual.mono fun _ h=>h.1

#print axioms dCoeff_pos
#print axioms d_size_literal_nat
#print axioms d_size_literal_cubic
#print axioms d_lambda_log_bound
#print axioms d_threshold_log_bound
#print axioms source_root_eventually_above_cutoff
end
end V8NativeMessage.N2DPost
