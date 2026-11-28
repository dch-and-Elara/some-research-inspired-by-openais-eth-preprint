import V8NativeMessageN2DCertLeaf
import P5D1LiteralPrinted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 29000000

/-! Substitute the actual four-copy CNF's root and tuning into the
every-leaf theorem. The threshold is uniform even in the coefficient
extension polynomial, whose printed degree varies with the input size. -/
namespace V8NativeMessage.N2DCert
open Real Filter Polynomial Paper5.HybridClosure Paper5.HybridClosure.Printed
  Paper5.D1Literal J6ActiveRun J6R9Recursive J6R10Reachable J6R12Blueprint
  J6R11Blueprint J1PPrinted V8NativeMessage.C3.NativeAssembly
  V8NativeMessage.N2DLabels V8NativeMessage.N2DPost
open scoped Classical Polynomial Topology BigOperators

noncomputable section

theorem actual_four_clone_leaf_uniform_numeric :
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (2*epsDen)^30*(3:ℕ)^10≤dLambda n ∧ 3≤dDelta n ∧
      nativeH (dSize n)<24*n ∧
      (∀ m : ℕ,(1-eta (dSize n))*((24*n:ℕ):ℝ)/32≤(m:ℝ) → nativeH (dSize n)<m) ∧
      eta (dSize n)<1 ∧
      dCoeff/2*rate n≤(1-eta (dSize n))*(nativeH (dSize n):ℝ)/32 := by
  apply eventually_atTop.1
  filter_upwards [d_lambda_tends_atTop.eventually
    (eventually_ge_atTop ((2*epsDen)^30*(3:ℕ)^10)),
    d_printed_eventual,certified_root_margin_eventually_implies_active,
    eta_on_cloned_size_eventually_below_half,eventually_ge_atTop (2:ℕ)]
    with n hLog hSource hRoot hEta hn
  refine ⟨hLog,hSource.2.2.1,hSource.1,hRoot,by linarith only [hEta],?_⟩
  calc
    _ = (1/2)*(dCoeff*rate n) := by ring
    _ ≤ (1/2)*((threshold n:ℝ)/32) :=
      mul_le_mul_of_nonneg_left (d_threshold_log_bound n hn) (by norm_num)
    _ = (1/2)*(nativeH (dSize n):ℝ)/32 := by
      rw [show threshold n=nativeH (dSize n) from rfl]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hEta] : (1/2:ℝ)≤1-eta (dSize n))
        (by positivity)) (by norm_num)

theorem actual_four_clone_every_D_leaf :
    ∃ N₀ : ℕ, ∀ {W : Type} [Fintype W] [DecidableEq W]
      (F : Finset (W×W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
      (ϕ : ℤ[X]) (σ : W→Bool) (hf : ϕ.Monic)
      (sel : CertifiedSelector (printedParams (f:=ϕ) (ell:=1) (oldRowSize F))
        (sourceDelta (oldRowSize F))),
      let n := Fintype.card W
      let root := oldRowRoot F cubic ϕ σ
      let B := sourceBlueprint (forget sel) root hf
      N₀≤n → ϕ.natDegree=4*dLambda n →
      (∀ w : (FactoryPlan (forget sel)).Slot root,
        nativeH (oldRowSize F)<((FactoryPlan (forget sel)).child root w).edges) ∧
      ∀ d : Call (PhysicalHost ϕ 1), Reach B.program root d →
        d.edges≤nativeH (oldRowSize F) →
        B.program.run d = J6ChildPlan.allBits d.edges
          (fun x=>reduce d.prec ϕ 1 (physicalEntries hf d x).prod) ∧
        dCoeff/2*rate n<logb 2 (paidLeafAssignments d.edges:ℝ) := by
  obtain ⟨N₀,numeric⟩ := actual_four_clone_leaf_uniform_numeric
  refine ⟨N₀,?_⟩
  intro W fi de F cubic f σ hf sel
  dsimp only
  intro hSize hDegree
  let n := Fintype.card W
  let root := oldRowRoot F cubic f σ
  have sz : oldRowSize F=dSize n := oldRowSize_eq_dSize F cubic
  obtain ⟨hLog,hDelta,hActive,hEach,hEta,hRate⟩ := numeric n hSize
  have hΔ : 3≤sourceDelta (oldRowSize F) := by rw [sz]; exact hDelta
  let cfg := creating_source_config F cubic f hDegree hLog
  let seed := oldRowRoot_stable F cubic f σ hΔ
  have hRootEdges : root.edges=24*n := d_physical_wire_count F cubic
  have hRootActive : nativeH (oldRowSize F)<root.edges := by
    rw [sz,hRootEdges]
    exact hActive
  refine ⟨?_,?_⟩
  · intro w
    have h := (certified_actual_child_margin cfg sel root seed w w.val.2.2.2).1
    rw [regroup_original_slot] at h
    let m := ((FactoryPlan (forget sel)).child root w).edges
    have hLower : (1-eta (dSize n))*((24*n:ℕ):ℝ)/32≤(m:ℝ) := by
      calc
        _ =(1-eta (oldRowSize F))*(root.edges:ℝ)/32 := by rw [sz,hRootEdges]
        _ ≤ _ := h
    exact (congrArg nativeH sz).trans_lt (hEach m hLower)
  · intro d seen hl
    have heta : eta (oldRowSize F)<1 := by rw [sz]; exact hEta
    obtain ⟨hRun,hCost⟩ :=
      printed_D_individually_requested_leaf cfg sel root seed hf hRootActive d heta seen hl
    rw [←sz] at hRate
    exact ⟨hRun,hRate.trans_lt hCost⟩

#print axioms actual_four_clone_leaf_uniform_numeric
#print axioms actual_four_clone_every_D_leaf
end
end V8NativeMessage.N2DCert
