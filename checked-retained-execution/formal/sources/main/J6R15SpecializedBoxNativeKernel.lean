import J6R15SpecializedBoxHalfConstants
import J6R9PacketScaled

/-! A canonical actual target kernel, including all higher terms needed
at the requested finite precision. It is the witnessed native crossing,
not only a polynomial sharing its first coefficient. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget P1DyadicGrid P1DyadicGridBridge
open J6R9PacketCoeff J8Physical J8EndToEnd DyadicProbeCompiler
open NativeProbeRing J6R9Recursive

noncomputable section
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

set_option linter.unusedSectionVars false in
def targetCrossing (he : Even L) (hL : 2<L) (s : S) (j : TargetPorts d s)
    (hj : j ∈ groupedTargets d s) :
    Crossing ((L:ℤ)-1) (d.seat (j.1.1,j.2)).2.val ((d.seat (pinWire d s)).2.val%2) 0 := by
  let u := integerDenominator d s j
  have hu : Odd u := (groupedTargets_denom d s he hL hj).2
  exact ⟨0,u,hu,le_rfl,by simp [pow₂]; rfl,(odd_valuation_zero hu).symm⟩

set_option linter.unusedSectionVars false in
def genuineCross (a p b : ℕ) (he : Even L) (hL : 2<L) (s : S)
    (j : TargetPorts d s) : Source[X] :=
  if hj : j ∈ groupedTargets d s then
    let cross := targetCrossing d he hL s j hj
    (modeHalf a p ((L:ℤ)-1) cross.oddPart cross.odd b).map twoLocalToSource.toRingHom
  else 0

set_option linter.unusedSectionVars false in
theorem genuine_kernel_is_own_divX (a p : ℕ) (hp : 0<p) (hW : L=2^a)
    (he : Even L) (hL : 2<L) (s : S) (b : ℕ) :
    physicalKernel d s he hL (J9FactorBounds.kernel L) b
      (fun j => (genuineCross d a p b he hL s j).divX) =
    genuineCross d a p b he hL s := by
  apply native_crossing_realized_by_own_tail d he hL s b
  · intro j hj
    simp only [genuineCross,dif_pos hj]
    exact halfMode_const_is_actual_J9 d a p hp hW he hL s b j hj (targetCrossing d he hL s j hj)
  · intro j hj
    simp only [genuineCross,dif_neg hj]

private theorem half_congr_odd (a p : ℕ) (t : ℤ) (b : ℕ)
    {u v : ℤ} (hu : Odd u) (hv : Odd v) (h : u=v) :
    modeHalf a p t u hu b = modeHalf a p t v hv b := by cases h; rfl

set_option linter.unusedSectionVars false in
theorem literal_target_mode_at_probe (a p : ℕ) (hp : 0<p) (hW : L=2^a)
    (he : Even L) (hL : 2<L) (s : S) (b : ℕ) (j : TargetPorts d s)
    (hj : j ∈ groupedTargets d s)
    (cross : Crossing ((L:ℤ)-1) (d.seat (j.1.1,j.2)).2.val ((d.seat (pinWire d s)).2.val%2) 0)
    (f : ℤ[X]) (ell : ℕ) (hnil : (2:Box f ell p)^p=0) (z : Scalar p f) :
    let v := J6ActiveInterpolation.scalarIn p f ell z
    J6R9PacketReceive.mode a p hnil (Nat.zero_le a) cross v b =
      (2:Box f ell p)^(a+1+b)*v *
        evalBox p f ell z (physicalKernel d s he hL (J9FactorBounds.kernel L) b
          (fun j => (genuineCross d a p b he hL s j).divX) j) := by
  dsimp only
  rw [actual_mode_is_explicit_half_poly, genuine_kernel_is_own_divX d a p hp hW he hL s b]
  simp only [genuineCross,dif_pos hj]
  let cn := targetCrossing d he hL s j hj
  have hu : cross.oddPart = cn.oddPart :=
    (crossing_zero_oddPart cross).trans (crossing_zero_oddPart cn).symm
  rw [half_congr_odd a p ((L:ℤ)-1) b cross.odd cn.odd hu]
  congr 1
  change (modeHalf a p ((L:ℤ)-1) cn.oddPart cn.odd b).eval₂
      (J6ZeroTransport.reduceAt p hnil) (2 * J6ActiveInterpolation.scalarIn p f ell z) =
    J6ActiveInterpolation.scalarIn p f ell
      (((modeHalf a p ((L:ℤ)-1) cn.oddPart cn.odd b).map twoLocalToSource.toRingHom).eval₂
        (toScalar p f) (2*z))
  have hh := native_eval_transports p f ell hnil (2*z) (modeHalf a p ((L:ℤ)-1) cn.oddPart cn.odd b)
  rw [map_mul,map_ofNat] at hh
  exact hh.symm

#print axioms targetCrossing
#print axioms genuineCross
#print axioms genuine_kernel_is_own_divX
#print axioms literal_target_mode_at_probe
end
end J6R14SpecializedBox
