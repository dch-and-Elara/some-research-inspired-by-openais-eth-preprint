import V8NativeMessageN2DCertPhysical
import V8NativeMessageN2DCertCutoffUpper
import V8NativeMessageN2DPostNumeric
import V8NativeMessageN2DPostPath

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 26000000

/-! Each individual leaf of the *same* live source program is bounded,
not just a branch that chooses a largest sibling. -/
namespace V8NativeMessage.N2DCert
open Real Filter Polynomial Paper5.HybridClosure.Printed J6ActiveRun J6R9Recursive
  J6R10Reachable J6R12Blueprint J6R11Blueprint J1PPrinted
  V8NativeMessage.C3.NativeAssembly V8NativeMessage.N2DLabels V8NativeMessage.N2DPost
open scoped Classical Polynomial Topology BigOperators

noncomputable section

variable {f : ℤ[X]} {ell s C : ℕ}
local notation "SP" => printedParams (f:=f) (ell:=ell) s
local notation "DELTA" => sourceDelta s

theorem regroup_original_slot (sel : Selector SP DELTA)
    (c : Call (PhysicalHost f ell)) (w : (FactoryPlan sel).Slot c) :
    regroupNative sel c w w.val.2.2.2=w := by
  rcases w with ⟨⟨t,z,m,g⟩,hw⟩
  rfl

theorem actual_terminal_reachable_eq (sel : Selector SP DELTA)
    {c d : Call (PhysicalHost f ell)}
    (h : NativeReach (FactoryPlan sel) c d) (hc : c.edges≤nativeH s) : d=c := by
  cases h with
  | reflexive => rfl
  | step w _ => exact (not_lt_of_ge hc w.property).elim

theorem certified_native_leaf_margin (cfg : RootBounds s C f)
    (sel : CertifiedSelector SP DELTA) {c d : Call (PhysicalHost f ell)}
    (h : NativeReach (FactoryPlan (forget sel)) c d) (seed : Stable s C c)
    (ha : nativeH s<c.edges) (hl : d.edges≤nativeH s) (hEta : eta s<1) :
    (1-eta s)*(nativeH s:ℝ)/32<(d.edges:ℝ) := by
  induction h with
  | reflexive c => exact (not_lt_of_ge hl ha).elim
  | @step c d w tail ih =>
    let next := (FactoryPlan (forget sel)).child c w
    have nextStable : Stable s C next := stable_step cfg (forget sel) seed w
    by_cases nextActive : nativeH s<next.edges
    · exact ih nextStable nextActive hl
    · have hEq : d=next := actual_terminal_reachable_eq (forget sel) tail
        (Nat.le_of_not_gt nextActive)
      have hLo := (certified_actual_child_margin cfg sel c seed w w.val.2.2.2).1
      rw [regroup_original_slot] at hLo
      have hHa : (nativeH s:ℝ)<(c.edges:ℝ) := by exact_mod_cast ha
      have hMul := mul_lt_mul_of_pos_left hHa (sub_pos.mpr hEta)
      have hFirst := div_lt_div_of_pos_right hMul (by norm_num : (0:ℝ)<32)
      rw [hEq]
      exact hFirst.trans_le hLo

theorem printed_each_root_child_eventually_active :
    ∀ᶠ N : ℕ in atTop,
      ∀ (f : ℤ[X]) (ell C : ℕ) (_cfg : RootBounds (dSize N) C f)
        (sel : CertifiedSelector (printedParams (f:=f) (ell:=ell) (dSize N)) (sourceDelta (dSize N)))
        (root : Call (PhysicalHost f ell)) (_seed : Stable (dSize N) C root)
        (_w : (FactoryPlan (forget sel)).Slot root),
        root.edges=24*N →
        nativeH (dSize N)<((FactoryPlan (forget sel)).child root _w).edges := by
  filter_upwards [certified_root_margin_eventually_implies_active] with N hCut
  intro f ell C cfg sel r seed w hr
  have hLo := (certified_actual_child_margin cfg sel r seed w w.val.2.2.2).1
  rw [regroup_original_slot,hr] at hLo
  exact hCut _ hLo

theorem printed_D_individually_requested_leaf (cfg : RootBounds s C f)
    (sel : CertifiedSelector SP DELTA) (root : Call (PhysicalHost f ell))
    (seed : Stable s C root) (hf : f.Monic) (hRoot : nativeH s<root.edges)
    (d : Call (PhysicalHost f ell)) (hEta : eta s<1)
    (seen : Reach (sourceBlueprint (forget sel) root hf).program root d)
    (leaf : d.edges≤nativeH s) :
    (sourceBlueprint (forget sel) root hf).program.run d =
      J6ChildPlan.allBits d.edges
        (fun x=>reduce d.prec f ell (physicalEntries hf d x).prod) ∧
      (1-eta s)*(nativeH s:ℝ)/32<logb 2 (paidLeafAssignments d.edges:ℝ) := by
  have hN : NativeReach (FactoryPlan (forget sel)) root d :=
    (paddedBlueprint_exact_reachable (J6R12Blueprint.N (forget sel)) (Childs (forget sel))
      root (positive_at_native (forget sel) root) f ell (physicalEntries hf) d).1 seen
  refine ⟨blueprint_leaf_formula (sourceBlueprint (forget sel) root hf) d leaf,?_⟩
  rw [leaf_log_exact]
  exact certified_native_leaf_margin cfg sel hN seed hRoot leaf hEta

theorem printed_D_each_leaf_eventually_omega :
    ∀ᶠ N : ℕ in atTop,
      ∀ (f : ℤ[X]) (ell C : ℕ) (_cfg : RootBounds (dSize N) C f)
        (sel : CertifiedSelector (printedParams (f:=f) (ell:=ell) (dSize N)) (sourceDelta (dSize N)))
        (root : Call (PhysicalHost f ell)) (_seed : Stable (dSize N) C root) (hf : f.Monic)
        (d : Call (PhysicalHost f ell)),
        let B := sourceBlueprint (forget sel) root hf
        root.edges=24*N →
        Reach B.program root d →
        d.edges≤nativeH (dSize N) →
        B.program.run d = J6ChildPlan.allBits d.edges
          (fun x=>reduce d.prec f ell (physicalEntries hf d x).prod) ∧
          dCoeff/2*rate N<logb 2 (paidLeafAssignments d.edges:ℝ) := by
  filter_upwards [eventually_ge_atTop (2:ℕ),eta_on_cloned_size_eventually_below_half,
    source_root_eventually_above_cutoff] with N hN hEta hAct
  intro f ell C cfg sel root seed hf d
  dsimp only
  intro hRoot seen hLeaf
  have hRoot' : nativeH (dSize N)<root.edges := by rw [hRoot]; exact hAct
  obtain ⟨hRun,hLog⟩ := printed_D_individually_requested_leaf cfg sel root seed hf hRoot' d
    (by linarith only [hEta]) seen hLeaf
  have hBase : (1/2:ℝ)≤1-eta (dSize N) := by linarith only [hEta]
  have hBound : dCoeff/2*rate N≤(1-eta (dSize N))*(nativeH (dSize N):ℝ)/32 := by
    calc
      _ =(1/2)*(dCoeff*rate N) := by ring
      _ ≤ (1/2)*((threshold N:ℝ)/32) :=
        mul_le_mul_of_nonneg_left (d_threshold_log_bound N hN) (by norm_num)
      _ =(1/2)*(nativeH (dSize N):ℝ)/32 := by
        rw [show threshold N=nativeH (dSize N) from rfl]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hBase (by positivity)) (by norm_num)
  exact ⟨hRun,hBound.trans_lt hLog⟩

#print axioms regroup_original_slot
#print axioms actual_terminal_reachable_eq
#print axioms certified_native_leaf_margin
#print axioms printed_each_root_child_eventually_active
#print axioms printed_D_individually_requested_leaf
#print axioms printed_D_each_leaf_eventually_omega
end
end V8NativeMessage.N2DCert
