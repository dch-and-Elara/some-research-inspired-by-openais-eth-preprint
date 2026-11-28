import V8NativeMessageC3HermiteNative
import HermiteLossReceive
import J6R9RecursiveNormalizer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

/-! Exact D weighted reconstruction stencil at the five-copy active sites. -/
namespace V8NativeMessage.C3.Hermite.D
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9Recursive J6R10Integral
open V8PooledMenu V8PooledMenu.FiveCopy V8PooledRange
open Canonical
noncomputable section

variable (V : Type) [Fintype V]

def dOrder (t : Site V) : ℕ :=
  J6ActiveSchedule.order (wireSize V) (rootU V) t.val

def dQuotientWeight (f : ℤ[X]) (t : Site V) (j : Fin (dOrder V t)) : RatRing f 1 :=
  algebraMap ℚ (RatRing f 1)
    (HermiteLoss.weight (rootA V) (rootU V) (printedH V) j.val t.val)

theorem d_quotient_weight_is_exact (f : ℤ[X]) (t : Site V) (j : Fin (dOrder V t)) :
    dQuotientWeight V f t j =
      (E (K:=RatRing f 1) (rootA V) (wireSize V) (rootU V) t.val).eval 0 *
        extrapolate (rootA V) t.val ^ j.val :=
  (exact_weight (K:=RatRing f 1) (rootA V) (wireSize V) (rootU V) j.val t.val).symm

theorem d_weight_fits (t : Site V) (hu : 0<rootU V) (hM : rootU V≤wireSize V)
    (j : Fin (dOrder V t)) :
    HermiteLoss.totalLoss (rootA V) (printedH V) j.val t.val ≤ ordinaryDLoss t := by
  obtain ⟨hg,hn⟩ := J6R9Recursive.active_grid (rootA V) (wireSize V) (rootU V) t.property
  have hl := HermiteLoss.level_grid_le hg hn
  have he : nodeD t=2^(rootA V-HermiteLoss.level t.val) := dyadic_div_pow hl
  have hj : j.val≤4*wireSize V :=
    j.isLt.le.trans (J6ActiveSchedule.order_bound (wireSize V) (rootU V) t.val hu hM)
  unfold HermiteLoss.totalLoss ordinaryDLoss
  rw [he]
  simp only [Nat.mul_assoc]
  apply Nat.add_le_add_left
  have hm := Nat.mul_le_mul hj (Nat.sub_le (rootA V+1) (HermiteLoss.level t.val))
  simpa only [Nat.mul_assoc] using hm

theorem d_quotient_weight_loss (f : ℤ[X]) (t : Site V)
    (hu : 0<rootU V) (hM : rootU V≤wireSize V) (j : Fin (dOrder V t)) :
    HasLoss f 1 (ordinaryDLoss t) (dQuotientWeight V f t j) := by
  obtain ⟨hg,hn⟩ := J6R9Recursive.active_grid (rootA V) (wireSize V) (rootU V) t.property
  let l := HermiteLoss.totalLoss (rootA V) (printedH V) j.val t.val
  let w := HermiteLoss.weight (rootA V) (rootU V) (printedH V) j.val t.val
  have hb : (2:ℚ)^l*w∈twoLocalSubalgebra :=
    HermiteLoss.weight_scaled_integral _ _ _ _ hg hn
  have hle : l≤ordinaryDLoss t := d_weight_fits V t hu hM j
  have hc : (2:ℚ)^ordinaryDLoss t*w∈twoLocalSubalgebra := by
    have he : (2:ℚ)^ordinaryDLoss t*w = (2:ℚ)^(ordinaryDLoss t-l)*((2:ℚ)^l*w) := by
      rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hle]
    rw [he]
    exact twoLocalSubalgebra.mul_mem (two_pow_local _) hb
  let u : TwoLocal := ⟨(2:ℚ)^ordinaryDLoss t*w,hc⟩
  refine ⟨localScalar f 1 u,?_⟩
  rw [embed_localScalar]
  change (2:RatRing f 1)^ordinaryDLoss t*algebraMap ℚ (RatRing f 1) w =
    algebraMap ℚ (RatRing f 1) ((2:ℚ)^ordinaryDLoss t*w)
  rw [map_mul,map_pow,map_ofNat]

#print axioms d_quotient_weight_is_exact
#print axioms d_weight_fits
#print axioms d_quotient_weight_loss
end
end V8NativeMessage.C3.Hermite.D