import V8NativeMessageN2DCertScale
import V8NativeMessageN2DCertMarginal
import V8NativeMessageN2DLabelsCore
import V8NativeMessageC3NativeAssemblyN2Path

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 26000000

/-! Transport the full-label margin to an actual emitted child, for
every group at the same selected slot. The original score is read
from this very call's actual certified packing. -/
namespace V8NativeMessage.N2DCert
open Real Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R12Blueprint
  J6R11Blueprint J6R10Repack J6R11Repack J1PPrinted J9PrintedSchedule P11FullPacking
  V8NativeMessage.C3.NativeAssembly V8NativeMessage.N2DLabels
open scoped Polynomial Classical BigOperators

noncomputable section

variable {f : ℤ[X]} {ell s C : ℕ}

theorem root_bounds_large_size (cfg : RootBounds s C f) : 2≤s := by
  by_contra! hs
  have hl : Nat.clog 2 s≤Nat.clog 2 1 := Nat.clog_mono_right 2 (by omega)
  simp at hl
  have h0 : Nat.clog 2 s=0 := by omega
  have hw := cfg.widthPos
  simp only [h0,rootU,Nat.zero_div] at hw
  omega

theorem certified_actual_child_margin (cfg : RootBounds s C f)
    (sel : CertifiedSelector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (c : Call (PhysicalHost f ell)) (seed : Stable s C c)
    (w : (FactoryPlan (forget sel)).Slot c) (g : Fin 64) :
    let m := ((FactoryPlan (forget sel)).child c (regroupNative (forget sel) c w g)).edges
    (1-eta s)*(c.edges:ℝ)/32≤(m:ℝ) ∧ (m:ℝ)≤(1+eta s)*(c.edges:ℝ)/32 := by
  let S := printedParams (f:=f) (ell:=ell) s
  let sel₀ := forget sel
  let d : Ready S (sourceDelta s) c := getReady cfg seed w.property
  let t := w.val.1
  let P := packing sel₀ d
  let i := centerIndex d t
  let gr := declaredGroup P.rowLabel P.colLabel i
  let m := ((FactoryPlan sel₀).child c (regroupNative sel₀ c w g)).edges
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  have hCount : Nat.card c.host.Edge=c.edges := (host_card c.host).trans d.edgeCount
  have hCell : Nat.card (Cells (S.levelBits c.depth))=stepD (Nat.clog 2 s) c.depth := by
    unfold Cells
    rw [total_cells,Fintype.card_fin]
    rfl
  have hm : m=Nat.card (ChildEdge c.host.network gr g) := by
    change ((FactoryPlan sel₀).child c (regroupNative sel₀ c w g)).edges=_
    rw [regroup_edgeCount sel₀ c w d g,Nat.card_eq_fintype_card]
    rfl
  have hv := exact_child_margin c.host.network P (sourceDelta s) (selected_variance sel d) i g
  let D := stepD (Nat.clog 2 s) c.depth
  let M : ℝ := c.edges
  let e := (D:ℝ)*sqrt (2*M*(sourceDelta s:ℝ))
  have hCore : M-e≤32*(m:ℝ) ∧ 32*(m:ℝ)≤M+e := by
    change (Nat.card c.host.Edge:ℝ)-(Nat.card (Cells (S.levelBits c.depth)):ℝ)*
      sqrt (2*(Nat.card c.host.Edge:ℝ)*(sourceDelta s:ℝ))≤
        32*(Nat.card (ChildEdge c.host.network gr g):ℝ) ∧
        32*(Nat.card (ChildEdge c.host.network gr g):ℝ)≤(Nat.card c.host.Edge:ℝ)+
          (Nat.card (Cells (S.levelBits c.depth)):ℝ)*sqrt (2*(Nat.card c.host.Edge:ℝ)*(sourceDelta s:ℝ))
        at hv
    rw [hCount,hCell,←hm] at hv
    exact hv
  have hAdd : e≤M*eta s := by
    change (D:ℝ)*sqrt (2*(c.edges:ℝ)*(sourceDelta s:ℝ))≤(c.edges:ℝ)*eta s
    rw [scale_call_error s c.edges D (Nat.zero_lt_of_lt d.active)]
    exact mul_le_mul_of_nonneg_left
      (uniform_call_error s c.edges c.depth (root_bounds_large_size cfg) cfg.widthPos d.active)
      (by positivity)
  change (1-eta s)*M/32≤(m:ℝ) ∧ (m:ℝ)≤(1+eta s)*M/32
  constructor
  · exact (div_le_iff₀ (by norm_num : (0:ℝ)<32)).2 (by nlinarith only [hCore.1,hAdd])
  · exact (le_div_iff₀ (by norm_num : (0:ℝ)<32)).2 (by nlinarith only [hCore.2,hAdd])

#print axioms root_bounds_large_size
#print axioms certified_actual_child_margin
end
end V8NativeMessage.N2DCert
