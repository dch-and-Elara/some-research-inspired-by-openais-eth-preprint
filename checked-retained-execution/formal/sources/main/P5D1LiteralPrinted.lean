import P5D1LiteralSelect
import P5HybridClosurePrintedEnd
import J6R11Threshold

/-! D1 at the literal original tuning and on the same E1 24N family.
The original dispatcher and bit upper/runtime are not manufactured from
the cardinal bound, which only lowers along an explicit paid trace. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral
  GroupProducts SeparatedRank GraphCutMoments EmpiricalCutMoments
open Paper5.HybridClosure.Printed (dSize dLambda dU dA dL dCells dDelta d_widths
  mainQ mainR mainCells printedExponent printed_exp_term_count)

section Sizes
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v,degree F v=3)
variable (f : ℤ[X])
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F cubic f (fun _ => false))

include cubic in
theorem oldRowSize_eq_dSize : oldRowSize F = dSize (Fintype.card W) := by
  have h := regular_edge_count F 3 cubic
  simp only [oldRowSize,dSize,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_coe]
  omega

include cubic in
theorem oldRow_widths_printed :
    (S).levelBits 0 = dA (Fintype.card W) ∧ (S).levelWidth 0 = dU (Fintype.card W) := by
  change stepA (Nat.clog 2 (oldRowSize F)) 0 = _ ∧ stepU (Nat.clog 2 (oldRowSize F)) 0 = _
  rw [oldRowSize_eq_dSize F cubic]
  exact ⟨(d_widths _).1, by simp [stepU_as_div,dU,dLambda]⟩

theorem rootKept_card_exact (d : Ready S Δ r*) :
    (rootKept F f).card = (S).levelWidth 0 := by
  let e : ↥(rootKept F f) ≃ Fin ((S).levelWidth 0) :=
    { toFun := fun i => ⟨i.val.val,(Finset.mem_filter.mp i.property).2⟩
      invFun := fun i => ⟨⟨i.val,i.isLt.trans_le d.widthFits⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.isLt⟩⟩
      left_inv := fun x => Subtype.ext (Fin.ext rfl)
      right_inv := fun x => Fin.ext rfl }
  simpa using Fintype.card_congr e

include cubic in
theorem creating_source_config
    (hdeg : f.natDegree = 4*dLambda (Fintype.card W))
    (hsize : (2*epsDen)^30*(3:ℕ)^10 ≤ dLambda (Fintype.card W)) :
    RootBounds (oldRowSize F) 3 f := by
  rw [oldRowSize_eq_dSize F cubic]
  obtain ⟨_,hs,hu⟩ := J6R11Threshold.printed_size_implies_numeric_guards (dSize (Fintype.card W)) 3
    (by decide) hsize
  exact ⟨hdeg,by decide,hs,hu,hsize⟩
end Sizes

section Print
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V × V)) (reg₀ : ∀ v,degree E v=3) (loop₀ : ∀ v,(v,v)∉E)
variable (f : ℤ[X])
local notation "F" => replacedEdges E reg₀
local notation "reg" => replaced_cubic E reg₀ loop₀
local notation "Ws" => Fintype.card (TriVertex V)
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F reg f (fun _ => false))

set_option maxHeartbeats 26000000 in
theorem original_printed_D1_finite
    (hdeg : f.natDegree = 4*dLambda Ws)
    (hsize : (2*epsDen)^30*(3:ℕ)^10 ≤ dLambda Ws)
    (hf : f.Monic) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (γ : ℚ) (hg : 0<γ) (hg₃ : γ≤3)
    (expand : ∀ U : Finset V, γ*(min U.card (Fintype.card V-U.card):ℕ)≤
      ((boundary E U).card:ℚ))
    (hr : Paper5.HybridClosure.Printed.Ready γ Ws) :
    ∃ (P : RootPacking F reg f) (d : Ready S Δ r*),
      2^(printedExponent γ Ws) ≤ Fintype.card (PublicSlot F reg f P d) ∧
      ∀ (run : FixedSchedule.Execution (PublicSlot F reg f P d)),
        2^(printedExponent γ Ws) ≤ run.cost := by
  classical
  have sz := oldRowSize_eq_dSize F reg
  have widths := oldRow_widths_printed F reg f
  have hΔ : 3 ≤ Δ := by rw [sz]; exact hr.dDegree
  have hactive : (S).cutoff < Fintype.card (DWire F) := by
    change J9PrintedSchedule.leafThreshold (oldRowSize F) (Nat.clog 2 (oldRowSize F)) < _
    rw [sz,d_physical_wire_count F reg]
    exact hr.dActive
  have hMC : 2*5*((mainR Ws)^(2*(mainQ Ws)))^2≤12*Ws := by
    change 2*5*(mainCells Ws)^2 ≤ 12*Ws
    exact (Nat.mul_le_mul_right _ (by decide : 2*5≤12)).trans (hr.mainLayout.trans (by omega))
  have hDC : 2*(J9PrintedSchedule.arrayCard ((S).levelBits 0))^2*Δ≤Nat.card (DWire F) := by
    rw [widths.1, sz, Nat.card_eq_fintype_card, d_physical_wire_count F reg]
    exact hr.dCollision
  have hDS : 2^((S).levelBits 0)*J9PrintedSchedule.arrayCard ((S).levelBits 0)≤Nat.card (DWire F) := by
    rw [widths.1,Nat.card_eq_fintype_card,d_physical_wire_count F reg]
    exact hr.dSlot
  have hF : 0 < f.natDegree := by
    have hLog : 0 < dLambda Ws := by
      have ho : 0 < J9PrintedSchedule.rootU (dLambda Ws) := hr.dNodes
      unfold J9PrintedSchedule.rootU at ho
      omega
    omega
  let cfg := creating_source_config F reg f hdeg hsize
  let d : Ready S Δ r* := getReady cfg (oldRowRoot_stable F reg f _ hΔ) hactive
  have keq : (rootKept F f).card = dU Ws := (rootKept_card_exact F reg f d).trans widths.2
  have k0 : (rootKept F f).Nonempty := Finset.card_pos.mp (keq.symm ▸ hr.dNodes)
  obtain ⟨i,hi⟩ := k0
  have hbudget := hr.unionBudget
  rw [←keq] at hbudget
  obtain ⟨_,_,P,_,_,hcard,_⟩ := oldRow_joint_E1_exact_menu E reg₀ loop₀ f cfg hΔ hactive
    hf hF γ hg hg₃ expand (mainQ Ws) (mainR Ws) ⟨0,hr.mainNodes⟩ hr.mainAlphabet
    ⟨i,hi⟩ hMC hr.mainGroups hDC hDS hbudget
  have lower : 2^(min (routeDepth (γ/3) Ws (mainQ Ws)) (routeDepth (γ/3) Ws (dU Ws))) ≤
      0+Fintype.card (PublicSlot F reg f P d) := by
    rw [zero_add,←keq]
    exact (Nat.pow_le_pow_right (by decide) (min_le_right _ _)).trans hcard
  have hc := printed_exp_term_count hr lower
  rw [zero_add] at hc
  exact ⟨P,d,hc,fun run => hc.trans (FixedSchedule.card_le_cost run)⟩
end Print

#print axioms oldRowSize_eq_dSize
#print axioms oldRow_widths_printed
#print axioms rootKept_card_exact
#print axioms creating_source_config
#print axioms original_printed_D1_finite
end Paper5.D1Literal
