import P5HybridDUnclonedGraph
import P5HybridClosurePrintedD
import J6R11Threshold

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 17000000
set_option exponentiation.threshold 1024

/-! Exact source sizes and the Appendix D guards for the uncloned
tree network. In particular the degree threshold is the growing
printed delta, not the constant maximum old degree. -/
namespace Paper5.HybridDUncloned
open Filter J1PPrinted J9PrintedSchedule
open Paper5.HybridClosure.Printed (clog_linear_tendsto)
open scoped Topology

noncomputable section

def sizeByN (n : ℕ) : ℕ := 2*n+3*n/2
def rootWidth (s : ℕ) : ℕ := rootU (Nat.clog 2 s)
def rootBits (s : ℕ) : ℕ := stepA (Nat.clog 2 s) 0
def rootLength (s : ℕ) : ℕ := stepL (Nat.clog 2 s) 0
def rootCells (s : ℕ) : ℕ := stepD (Nat.clog 2 s) 0

theorem size_by_n_bounds (n : ℕ) : n≤sizeByN n ∧ sizeByN n≤4*n := by
  unfold sizeByN
  omega

theorem sourceSize_eq_sizeByN {W : Type} [Fintype W] [DecidableEq W]
    (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3) :
    sourceSize F=sizeByN (Fintype.card W) := by
  have h := literal_size_exact F cubic
  unfold sizeByN
  omega

theorem printed_dimension_words (s : ℕ) :
    rootBits s=2*rootWidth s ∧ rootLength s=2^rootBits s ∧
    rootCells s=64^(2*rootBits s) := by
  have h : rootBits s=2*rootWidth s := by
    simp [rootBits,rootWidth,stepA,stepU_as_div,rootU]
  exact ⟨h,rfl,rfl⟩

structure RootTune (s M : ℕ) : Prop where
  active : leafThreshold s (Nat.clog 2 s) < M
  width : 2≤rootWidth s
  degree : 3≤sourceDelta s
  collision : 2*(rootCells s)^2*sourceDelta s≤M
  slots : rootLength s*rootCells s≤M
  packetDegree : 2*rootLength s≤sourceDelta s

private theorem threshold_le_size (s d : ℕ) (hd : 0<d) : (s+d-1)/d≤s := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hd).2
  have h : s≤s*d := by simpa using Nat.mul_le_mul_left s (show 1≤d by omega)
  rw [show (s+1)*d=s*d+d by ring]
  omega

theorem source_numeric_tune (n : ℕ) (hn : 0<n)
    (hw : 2≤rootWidth (sizeByN n)) : RootTune (sizeByN n) (10*n) := by
  let s := sizeByN n
  let lam := Nat.clog 2 s
  have hl : 0<lam := by
    change 2≤lam/131072 at hw
    omega
  have hu : 1≤rootU (Nat.clog 2 s) := (by decide : (1:ℕ)≤2).trans hw
  have hS := (size_by_n_bounds n).2
  have ha : leafThreshold s lam<10*n :=
    (threshold_le_size s lam.sqrt (Nat.sqrt_pos.mpr hl)).trans_lt (by omega)
  have hg := source_packing_conditions s (10*n) 0 hu ha
  change 2*(rootCells s)^2*sourceDelta s≤10*n ∧
    rootLength s*rootCells s≤10*n ∧ 2*rootLength s≤sourceDelta s at hg
  have hL : 4≤rootLength s := stepL_ge_four _ 0 hu
  have hp := hg.2.2
  have hD : 3≤sourceDelta s := by omega
  exact ⟨ha,hw,hD,hg.1,hg.2.1,hp⟩

theorem source_actual_tune {W : Type} [Fintype W] [DecidableEq W]
    (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3)
    (hn : 0<Fintype.card W) (hw : 2≤rootWidth (sourceSize F)) :
    RootTune (sourceSize F) (Fintype.card (Wire F)) := by
  rw [sourceSize_eq_sizeByN F cubic] at hw ⊢
  rw [physical_wire_count F cubic]
  exact source_numeric_tune _ hn hw

theorem dimension_growing_slack {s M : ℕ} (T : RootTune s M) :
    (rootLength s)^1000<s ∧ (rootCells s)^1000<s :=
  dimensions_small s 0 (by have h := T.width; unfold rootWidth at h; omega)

theorem source_numeric_guards_eventually :
    ∀ᶠ n : ℕ in atTop,
      (2*epsDen)^30*(3:ℕ)^10≤Nat.clog 2 (sizeByN n) ∧
      RootTune (sizeByN n) (10*n) := by
  have hclog : Tendsto (Nat.clog 2) atTop atTop := by
    simpa only [one_mul,add_zero] using clog_linear_tendsto 1 0 (by decide)
  let bar : ℕ := max ((2*epsDen)^30*(3:ℕ)^10) 262144
  filter_upwards [eventually_gt_atTop (0:ℕ),hclog.eventually (eventually_ge_atTop bar)] with n hn hLog
  have hB := hLog.trans (Nat.clog_mono_right 2 (size_by_n_bounds n).1)
  have hw : 2≤rootWidth (sizeByN n) := by
    have h := (le_max_right ((2*epsDen)^30*(3:ℕ)^10) (262144:ℕ)).trans hB
    change 2≤Nat.clog 2 (sizeByN n)/131072
    omega
  exact ⟨(le_max_left _ _ : _≤bar).trans hB,source_numeric_tune n hn hw⟩

#print axioms size_by_n_bounds
#print axioms sourceSize_eq_sizeByN
#print axioms printed_dimension_words
#print axioms source_numeric_tune
#print axioms source_actual_tune
#print axioms dimension_growing_slack
#print axioms source_numeric_guards_eventually
end
end Paper5.HybridDUncloned
