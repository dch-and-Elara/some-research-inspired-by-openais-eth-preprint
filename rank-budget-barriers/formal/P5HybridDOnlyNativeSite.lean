import P5D1LiteralPrinted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000
set_option maxRecDepth 3500

/-! Original §8 lines 2114–2124, on the cloned D input. Two actual
finite root coordinates, one common EntryFile layout for any sign word,
and no identification of the two section-8 group functions with
individual native coefficients. -/
namespace Paper5.HybridDOnly
open scoped Classical Polynomial BigOperators
open Polynomial P1DyadicGrid P11FullPacking Paper5.HybridClosure
open J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun J6R12Blueprint
open Paper5.D1Literal J6ActiveSchedule J6R9Recursive J1PPrinted
open Paper5.HybridClosure.Printed (dLambda dSize dU dA dCells dL dDelta d_printed_feasible)

section NativeSite
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable (f : ℤ[X])
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "root" => oldRowRoot F reg f (fun _=>false)
local notation "M" => Fintype.card (DWire F)

theorem true_center_for_retained (d : Ready S Δ root) (i : rootKept F f) :
    ∃ t : PublicCenter F reg f,
      PublicIndex F reg f d t=i.val ∧ registerPrecision S root t =
        J9PrintedSchedule.precision (4*Fintype.card W+1)
          (HermiteLoss.sourceH M ((S).levelWidth 0)) (2^((S).levelBits 0-i.val.val)) M ((S).levelBits 0) := by
  let u := (S).levelWidth 0
  let a := (S).levelBits 0
  let t := P1DyadicGrid.pow₂ i.val.val
  have hi : i.val.val<u := (Finset.mem_filter.mp i.property).2
  have hu : 0<u := Nat.zero_lt_of_lt hi
  have hM : 0<M := (Nat.zero_le _).trans_lt d.active
  have hpos : 0<t := P1DyadicGrid.pow₂_pos _
  have htop : t < P1DyadicGrid.pow₂ a :=
    pow_lt_pow_right₀ (by decide : (1:ℤ)<2) i.val.isLt
  have ht : padicValInt 2 t=i.val.val := by
    simpa [t] using
      P1DyadicGrid.valuation_pow₂_mul_odd i.val.val (by decide : Odd (1:ℤ))
  have hc := J9PrintedSchedule.le_roundup_mul (3*M) u hu
  change 3*M≤height M u*u at hc
  have hp : 0<height M u := by
    by_contra h
    rw [Nat.eq_zero_of_not_pos h,zero_mul] at hc
    omega
  have gridT : t ∈ grid a := by
    apply mem_grid.mpr
    have hg := P1DyadicGrid.pow₂_pos a
    exact ⟨by linarith only [hpos,hg],htop⟩
  have act : t∈J6ActiveSchedule.active a M u := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpos.ne',gridT⟩,?_⟩
    unfold J6ActiveSchedule.order
    rw [ht]
    exact Nat.mul_pos hp (Nat.sub_pos_of_lt hi)
  let v : PublicCenter F reg f := ⟨t,act⟩
  refine ⟨v,Fin.ext ht,?_⟩
  change childPrecision (4*Fintype.card W+1) a M u t=_
  rw [J6R9Recursive.precision_same (4*Fintype.card W+1) a M u act]
  rw [show HermiteLoss.level t=i.val.val from ht]

end NativeSite

section RootSelector
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable (f : ℤ[X]) (P : RootPacking F reg f) (σ : W→Bool)
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "root" => oldRowRoot F reg f σ

theorem same_native_root_packing (d : Ready S Δ root) :
    packing (rootSel F reg f P σ) d = P :=
  sameRootSelector_pins S Δ root P d

end RootSelector

#print axioms true_center_for_retained
#print axioms same_native_root_packing
end Paper5.HybridDOnly
