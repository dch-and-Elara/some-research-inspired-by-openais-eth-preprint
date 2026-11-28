import A1R43LiteralFixedState
import A1R43LiteralBank
import A1R43LiteralOrigin
import J6R12Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option maxRecDepth 1800

/-! Every part of the original named-register instance is supplied by
the printed construction: independent simulated words, full physical
slot chart, real f and its exact finite probe word capacity. -/
namespace A1R43Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R12Repack J6R12Blueprint
open J6ActiveRun J1PPrinted J6R9Recursive
noncomputable section
attribute [local irreducible] A1R43Literal.starRoot
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
local notation "WPlan" => PairPlan F (smallA m) (copies m)

theorem eligible_probe_bank_on_star (W : WPlan) (guard : PrintedMargins m)
    (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (f : ℤ[X]) (cfg : RootBounds s 1 f)
    (words : Fin (2^(4*Nat.clog 2 s))→Fin f.natDegree→Bool)
    (hfirst : words ⟨0,pow_pos (by decide) _⟩=(fun _=>false))
    (hwords : ∀ p,0<p→∀ i j,i≠j →
      IsUnit (NativeProbeRing.probe p f (words j)-NativeProbeRing.probe p f (words i))) :
    Nonempty (EligibleBank f (J9PrintedSchedule.degreeBound (starRoot F W f).edges (2^nativeA m))) := by
  let r := starRoot F W f
  let S := printedParams (f:=f) (ell:=1) s
  let d := star_ready F W f guard cubic cfg.coefficient cfg.size
  let D := J9PrintedSchedule.degreeBound r.edges (2^nativeA m)
  have he : S.levelBits r.depth=nativeA m := (root_bits F W f guard).trans guard.full_dim
  have hBank : D+1≤2^(4*Nat.clog 2 s) := by
    have hh := @J6R12Blueprint.Ready.fit f 1 S (sourceDelta s) r d
    change J9PrintedSchedule.probeCount r.edges (2^S.levelBits r.depth)≤2^f.natDegree at hh
    rw [he,cfg.coefficient] at hh
    exact hh
  exact ⟨eligiblePrefix f D (4*Nat.clog 2 s) hBank words hfirst hwords⟩

theorem original_A1_input_and_bank (hm : 0<m) (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (large : (2*epsDen)^30*(1:ℕ)^10≤Nat.clog 2 s) :
    ∃ (f : ℤ[X]) (W : WPlan) (guard : PrintedMargins m) (cfg : RootBounds s 1 f) (hf : f.Monic),
      Irreducible (NativeProbeRing.residuePoly f) ∧
      Nonempty (EligibleBank f (J9PrintedSchedule.degreeBound (starRoot F W f).edges (2^nativeA m))) ∧
      let r := starRoot F W f
      let S := printedParams (f:=f) (ell:=1) s
      let d := star_ready F W f guard cubic cfg.coefficient cfg.size
      let t := negativeCenter F W f guard
      let p := @J6ActiveRun.registerPrecision (J6R11Blueprint.PhysicalHost f 1) Unit S r t
      letI := r.host.finiteEdge
      letI := r.host.finiteRow
      letI := r.host.finiteCol
      (J6R14ZeroMode.polynomial (packing (starSelector F W f guard) d)
        (centerIndex d t) t.val p r.host.file hf).eval 0 =
        (independentCount F:Box f 1 p) := by
  obtain ⟨f,cfg,hf,hfield,words,hfirst,hwords⟩ := J6R12Bounds.sourceField_of_printed_guard s 1 (by decide) large
  let guard := printed_margins m hm cfg.widthPos
  obtain ⟨W⟩ := legal_plan_exists F cubic guard
  refine ⟨f,W,guard,cfg,hf,hfield,
    eligible_probe_bank_on_star F W guard cubic f cfg words hfirst (fun p hp=>(hwords p hp).2),?_⟩
  let d := star_ready F W f guard cubic cfg.coefficient cfg.size
  let t := negativeCenter F W f guard
  let p := @J6ActiveRun.registerPrecision (J6R11Blueprint.PhysicalHost f 1) Unit
    (printedParams (f:=f) (ell:=1) s) (starRoot F W f) t
  exact chosen_source_star_polynomial F W f guard cubic d p
    (@J6R12Blueprint.register_positive f 1 _ _ (starRoot F W f) d t)
    hf (J6R12Bounds.positive_degree cfg)

#print axioms eligible_probe_bank_on_star
#print axioms original_A1_input_and_bank
end
end A1R43Literal
