import V8NativeMessageC3NativeAssemblyN2MainMarginal
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12500000

/-! Binary logarithms of the ACTUAL second-pass visit counters.
No representative-search or bit-time assumption is added. -/
namespace V8NativeMessage.N2PostBounds
open Real V8NativeMessage.C3.NativeAssembly.MainScan
open scoped BigOperators Classical

noncomputable section

theorem log_from_nat_power_bound {m r T : ℕ} (hr : 0<r)
    (h : (2:ℕ)^m≤T^r) : (m:ℝ)/(r:ℝ)≤logb 2 (T:ℝ) := by
  have hc : (2:ℝ)^m≤(T:ℝ)^r := by exact_mod_cast h
  have hraw := logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (by positivity : 0<(2:ℝ)^m) hc
  have h2 : logb 2 2=1 := by simp
  simp only [logb_pow,h2,mul_one] at hraw
  apply (div_le_iff₀ (by exact_mod_cast hr : 0<(r:ℝ))).mpr
  simpa only [mul_comm] using hraw

theorem log_pow_two (m : ℕ) :
    logb 2 (((2:ℕ)^m:ℕ):ℝ)=(m:ℝ) := by
  have h2 : logb 2 2=1 := by simp
  rw [Nat.cast_pow,Nat.cast_ofNat,logb_pow,h2,mul_one]

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}
variable (hreg : ∀ v,GraphCutMoments.degree F v=3)

theorem literal_whole_log (L : CloneTuple F r Q J) (s : W→Bool)
    (h : feasible L.frame) (hr : 0<r) :
    ((4*Fintype.card W:ℕ):ℝ)/(r:ℝ)≤logb 2 ((nativeScan F hreg L s).1:ℝ) :=
  log_from_nat_power_bound hr (native_four_copy_N2 F hreg L s h hr)

theorem literal_rejected_zero (L : CloneTuple F r Q J) (s : W→Bool)
    (bad : ¬feasible L.frame) : nativeScan F hreg L s=(0,0,0) := by
  unfold nativeScan acceptedRun
  exact dif_neg bad

theorem literal_individual_log (L : Fin Q→CloneTuple F r Q J) (s : W→Bool)
    (hXi : xi (fun t => (L t).frame.group) ≤
      2*(Fintype.card (Fin Q):ℝ)*Fintype.card (Clone W))
    (t : Fin Q) (g : Fin r) (hf : feasible (L t).frame) :
    logb 2 ((secondScan (L t).frame (nativeGroup F hreg (L t) s) hf g).1:ℝ) =
      (sizeAt (fun u=>(L u).frame.group) t g:ℝ) ∧
    ((4*Fintype.card W:ℕ):ℝ)/(r:ℝ) -
      sqrt (2*(Q:ℝ)*((4*Fintype.card W:ℕ):ℝ)) ≤
      logb 2 ((secondScan (L t).frame (nativeGroup F hreg (L t) s) hf g).1:ℝ) := by
  obtain ⟨hT,hLow⟩ := individual_source_group_N2 F hreg L s hXi t g hf
  have hLog : logb 2 ((secondScan (L t).frame (nativeGroup F hreg (L t) s) hf g).1:ℝ) =
      (sizeAt (fun u=>(L u).frame.group) t g:ℝ) := by
    rw [hT]
    exact log_pow_two _
  refine ⟨hLog,?_⟩
  rw [hLog]
  simpa only [meanSize,Clone,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm (Fintype.card W) 4]
    using hLow

#print axioms log_from_nat_power_bound
#print axioms log_pow_two
#print axioms literal_whole_log
#print axioms literal_rejected_zero
#print axioms literal_individual_log
end
end V8NativeMessage.N2PostBounds
