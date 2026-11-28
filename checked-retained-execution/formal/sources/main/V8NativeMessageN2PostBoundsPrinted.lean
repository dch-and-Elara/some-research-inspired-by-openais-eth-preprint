import V8NativeMessageN2PostBoundsVisits
import V8NativeMessageN2PostBoundsBalance

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 19000000

/-! Uniform actual MAIN assertions of original v8 TeX 2179--2193 and
2218--2227. Eventual thresholds depend on the fixed printed schedule
(and on epsilon for the local relative error), not on the graph, public
tuple, requested group, signs, or the output's value. -/
universe u

namespace V8NativeMessage.N2PostBounds
open Real Filter P5MainBalance V8NativeMessage.C3.NativeAssembly.MainScan
open scoped Topology Classical

noncomputable section

abbrev mainR (W : Type u) [Fintype W] := mainAlphabet (4*Fintype.card W)

abbrev mainQ (W : Type u) [Fintype W] := mainNodes (4*Fintype.card W)

def originalXi {W : Type u} [Fintype W] {F : Finset (W×W)} {J : ℕ}
    (L : Fin (mainQ W)→CloneTuple F (mainR W) (mainQ W) J) : Prop :=
  xi (fun t=>(L t).frame.group) ≤
    2*(Fintype.card (Fin (mainQ W)):ℝ)*Fintype.card (Clone W)

theorem printed_completed_source_omega :
    ∃ N₀ : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W],N₀≤Fintype.card W →
      ∀ (F : Finset (W×W)) (cubic : ∀ v,GraphCutMoments.degree F v=3) (J : ℕ)
        (L : CloneTuple F (mainR W) (mainQ W) J) (s : W→Bool),
        feasible L.frame →
          mainCoeff*workScale (Fintype.card W) ≤ logb 2 ((nativeScan F cubic L s).1:ℝ) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp printed_mean_eventually
  refine ⟨K,?_⟩
  intro W _ _ hSize F cubic J L s h
  have hNum := hK (Fintype.card W) hSize
  exact hNum.2.trans (literal_whole_log cubic L s h hNum.1)

theorem printed_individual_source_relative (ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W],N₀≤Fintype.card W →
      ∀ (F : Finset (W×W)) (cubic : ∀ v,GraphCutMoments.degree F v=3) (J : ℕ)
        (L : Fin (mainQ W)→CloneTuple F (mainR W) (mainQ W) J) (s : W→Bool),
        originalXi L →
        ∀ (t : Fin (mainQ W)) (g : Fin (mainR W)) (hf : feasible (L t).frame),
          (1-ε)*wordMean (Fintype.card W) ≤
            logb 2 ((secondScan (L t).frame (nativeGroup F cubic (L t) s) hf g).1:ℝ) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (published_gap_eventually_small ε hε)
  refine ⟨K,?_⟩
  intro W _ _ hSize F cubic J L s hXi t g hf
  let N := Fintype.card W
  have hGap := (hK N hSize).2
  have hLow := (literal_individual_log cubic L s hXi t g hf).2
  calc
    (1-ε)*wordMean N = wordMean N-ε*wordMean N := by ring
    _ ≤ wordMean N-sqrt (2*(mainNodes (4*N):ℝ)*((4*N:ℕ):ℝ)) :=
      sub_le_sub_left hGap _
    _ ≤ _ := hLow

theorem printed_individual_source_omega :
    ∃ N₀ : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W],N₀≤Fintype.card W →
      ∀ (F : Finset (W×W)) (cubic : ∀ v,GraphCutMoments.degree F v=3) (J : ℕ)
        (L : Fin (mainQ W)→CloneTuple F (mainR W) (mainQ W) J) (s : W→Bool),
        originalXi L →
        ∀ (t : Fin (mainQ W)) (g : Fin (mainR W)) (hf : feasible (L t).frame),
          (mainCoeff/2)*workScale (Fintype.card W) ≤
            logb 2 ((secondScan (L t).frame (nativeGroup F cubic (L t) s) hf g).1:ℝ) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp printed_mean_eventually
  obtain ⟨K',hLocal⟩ := printed_individual_source_relative (1/2) (by norm_num)
  refine ⟨max K K',?_⟩
  intro W _ _ hSize F cubic J L s hXi t g hf
  let N := Fintype.card W
  have hMean := (hK N ((le_max_left _ _).trans hSize)).2
  have hOne := hLocal ((le_max_right _ _).trans hSize) F cubic J L s hXi t g hf
  have he : (mainCoeff/2)*workScale N ≤ (1-(1/2:ℝ))*wordMean N := by
    have H := mul_le_mul_of_nonneg_left hMean (by norm_num : 0≤(1/2:ℝ))
    linarith only [H]
  exact he.trans hOne

#print axioms originalXi
#print axioms printed_completed_source_omega
#print axioms printed_individual_source_relative
#print axioms printed_individual_source_omega
end
end V8NativeMessage.N2PostBounds
