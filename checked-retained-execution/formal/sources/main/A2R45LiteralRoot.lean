
import A2R45LiteralFixedState
import A2R45LiteralRuntimeHelpers
import J6R12Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4900000
set_option maxRecDepth 2200
set_option synthInstance.maxHeartbeats 130000
set_option linter.unusedSectionVars false

/-! The fixed completed zero mode is the actual printed plan's run,
with local truth computed by its real physical switch table. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R10Integral J6R11Integral J6R11Repack J6R12Repack
open J6R12Blueprint J6ActiveRun J6ActiveSchedule J1PPrinted J6R9Recursive
open FixedHostAcquisition J6R11Blueprint
noncomputable section
attribute [local irreducible] A2R45Literal.rootCall J6R12Blueprint.printedParams
variable {n : ℕ} (W : Plan n) (w : Input n) (f : ℤ[X])
local notation "m" => simCount n
local notation "s" => A1R43Literal.starSize m
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s
local notation "root" => rootCall W w f

theorem physical_zero_constant (guard : A1R43Literal.PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 S Δ root) (hf : f.Monic) (hF : 0<f.natDegree) (hn : 0<n) :
    @zeroValue f s (fixedSelector W w f guard) root d (negativeCenter W w f guard) hf
      (count w.enabled) := by
  let t := negativeCenter W w f guard
  let p := @J6ActiveRun.registerPrecision (PhysicalHost f 1) Unit S root t
  unfold zeroValue J6R14ZeroMode.physicalZeroP
  exact actual_chosen_source_polynomial W w f guard d p
    (@J6R12Blueprint.register_positive f 1 S Δ root d t) hf hF hn
theorem actual_count_fits (guard : A1R43Literal.PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 S Δ root) :
    count w.enabled<2^(registerPrecision S root (negativeCenter W w f guard)) := by
  let t := negativeCenter W w f guard
  let p := @J6ActiveRun.registerPrecision (PhysicalHost f 1) Unit S root t
  have hM : 0<(root).edges := (Nat.zero_le _).trans_lt d.active
  have hp : (root).prec<p :=
    child_monotone (root).prec ((S).levelBits (root).depth) (root).edges ((S).levelWidth (root).depth) t.val hM
  have hbase : (root).prec=n+2 := by unfold rootCall; rfl
  have hx : n+1<(root).prec := hbase.symm ▸ Nat.lt_succ_self (n+1)
  exact (count_le w.enabled).trans_lt
    (Nat.pow_lt_pow_right (by decide) (hx.trans hp))
theorem actual_fixed_slot_integer (guard : A1R43Literal.PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 S Δ root) (cfg : RootBounds s 1 f)
    (hf : f.Monic) (hF : 0<f.natDegree) (hn : 0<n)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    @zeroRead f s (fixedSelector W w f guard) root d (negativeCenter W w f guard) hf
      =count w.enabled := by
  exact @zeroRead_exact f s 1 (fixedSelector W w f guard) root d
    (negativeCenter W w f guard) hf inferInstance cfg (root_stable W w f guard) hF
    (count w.enabled) (actual_count_fits W w f guard d) (physical_zero_constant W w f guard d hf hF hn)

theorem same_mode_when_zero_omitted (guard : A1R43Literal.PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 S Δ root) (cfg : RootBounds s 1 f)
    (hf : f.Monic) (hF : 0<f.natDegree) (hn : 0<n)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (bank : J6R14ZeroMode.Prescribed f
      (J9PrintedSchedule.degreeBound (root).edges (2^((S).levelBits (root).depth)))) :
    @recoverRead f s (fixedSelector W w f guard) root d (negativeCenter W w f guard) hf bank
      =count w.enabled := by
  exact (@recoverRead_eq_zeroRead f s 1 (fixedSelector W w f guard) root d
    (negativeCenter W w f guard) hf inferInstance cfg (root_stable W w f guard) hF bank).trans
    (actual_fixed_slot_integer W w f guard d cfg hf hF hn)

omit W w in
theorem fixed_chart_before_every_input (guard : A1R43Literal.PrintedMargins m)
    (cfg : RootBounds s 1 f) (hf : f.Monic) (hF : 0<f.natDegree) (hn : 0<n)
    (deg : f.natDegree=4*Nat.clog 2 s)
    (large : (2*epsDen)^30*(1:ℕ)^10≤Nat.clog 2 s)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    ∃ P : Plan n,∀ u : Input n,
      @zeroRead f s (fixedSelector P u f guard) (rootCall P u f) (root_ready P u f guard deg large)
        (negativeCenter P u f guard) hf =count u.enabled := by
  obtain ⟨P⟩ := fixed_plan_exists (n:=n) guard
  exact ⟨P,fun u=>actual_fixed_slot_integer P u f guard (root_ready P u f guard deg large) cfg hf hF hn⟩

#print axioms physical_zero_constant
#print axioms actual_count_fits
#print axioms actual_fixed_slot_integer
#print axioms same_mode_when_zero_omitted
#print axioms fixed_chart_before_every_input
end
end A2R45Literal
