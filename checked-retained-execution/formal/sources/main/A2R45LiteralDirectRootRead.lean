import A2R45LiteralDirectAdmission
import A2R45LiteralRuntimeHelpers

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13500000
set_option synthInstance.maxHeartbeats 180000
set_option maxRecDepth 2450
set_option linter.unusedSectionVars false

/-! The direct-path CNF count from the actually printed completed
zero-mode root query, not a freely selected precision or logical count
callback. Source layout construction time is a separate claim. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial Std.Sat J7R9Compiler J6R11Blueprint J6R12Blueprint J6R12Repack
open A1R43Literal A1R43Literal.General J6R10Repack J6R11Integral J6R9Recursive
open J6ActiveRun J6ActiveSchedule J1PPrinted P11FullPacking

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V) (W : DirectPlan F) (f : ℤ[X])
local notation "m" => directM F
local notation "s" => starSize m
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s
local notation "root" => directRoot F W f

theorem direct_chosen_polynomial (guard : PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 S Δ root) (p : ℕ)
    (hp : 0<p) (hf : f.Monic) (hF : 0<f.natDegree) (occurs : AllOccur F) :
    letI := (root).host.finiteEdge
    letI := (root).host.finiteRow
    letI := (root).host.finiteCol
    let t := directNegative F W f guard
    (J6R14ZeroMode.polynomial
      (@packing f 1 S Δ root (directSelector F W f guard) d)
      (@centerIndex f 1 S Δ root d t) t.val p (root).host.file hf).eval 0 =
        (PinnedCNF.modelCount F:Box f 1 p) := by
  dsimp only
  letI : Fintype (DirectPad F W) := directPadFinite F W
  let P : PhysicalPacking (directPhysical (Pad:=DirectPad F W) F)
      ((S).levelBits (root).depth) (Fin 64) :=
    @packing f 1 S Δ root (directSelector F W f guard) d
  let i := @centerIndex f 1 S Δ root d (directNegative F W f guard)
  have hi := direct_negative_index F W f guard d
  change (J6R14ZeroMode.polynomial P i (-1) p (directNativeFile F f (Fintype.card V+1)) hf).eval 0 = _
  rw [J6R15PlantedIdentity.zero_eq_parentJet P i (minus_one_mem_grid _)
    (by decide : (-1:ℤ)≠0) (minus_one_odd_index _ i hi) p hp _ hf]
  exact direct_literal_parent_minus_one F P f p hf hF
    (direct_root_selected_pair F W f guard d) occurs

attribute [local irreducible] A2R45Literal.directRoot J6R12Blueprint.printedParams

theorem source_A2_direct_completed_slot (width : ∀ cl∈F,cl.length≤3)
    (guard : PrintedMargins m) (d : @J6R12Blueprint.Ready f 1 S Δ root)
    (cfg : RootBounds s 1 f) (hf : f.Monic) (hF : 0<f.natDegree) (occurs : AllOccur F)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    @zeroRead f s (directSelector F W f guard) root d (directNegative F W f guard) hf =
      PinnedCNF.modelCount F := by
  let t := directNegative F W f guard
  let p := @J6ActiveRun.registerPrecision (PhysicalHost f 1) Unit S root t
  have hp0 : 0<p := @register_positive f 1 S Δ root d t
  have fit : PinnedCNF.modelCount F<2^p := by
    have hp : (root).prec<p := child_monotone (root).prec ((S).levelBits (root).depth)
      (root).edges ((S).levelWidth (root).depth) t.val ((Nat.zero_le _).trans_lt d.active)
    have b : (root).prec=Fintype.card V+1 := by unfold directRoot; rfl
    have hp' : Fintype.card V+1<p := b ▸ hp
    have hf' : PinnedCNF.modelCount F<2^(Fintype.card V+1) := raw_models_fit F f
    exact hf'.trans (Nat.pow_lt_pow_right (by decide) hp')
  have eq : @zeroValue f s (directSelector F W f guard) root d t hf (PinnedCNF.modelCount F) := by
    unfold zeroValue J6R14ZeroMode.physicalZeroP
    exact direct_chosen_polynomial F W f guard d p hp0 hf hF occurs
  exact @zeroRead_exact f s 1 (directSelector F W f guard) root d t hf inferInstance cfg
    (direct_root_stable F W f width guard) hF _ fit eq

omit W in
theorem source_A2_direct_actual_one_query (width : ∀ cl∈F,cl.length≤3)
    (guard : PrintedMargins m) (cfg : RootBounds s 1 f) (hf : f.Monic)
    (hF : 0<f.natDegree) (occurs : AllOccur F)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    ∃ W : DirectPlan F,
      @zeroRead f s (directSelector F W f guard) (directRoot F W f)
        (direct_root_ready F W f width guard cfg) (directNegative F W f guard) hf =
      PinnedCNF.modelCount F := by
  obtain ⟨P⟩ := direct_actual_plan_exists F width guard
  exact ⟨P,source_A2_direct_completed_slot F P f width guard
    (direct_root_ready F P f width guard cfg) cfg hf hF occurs⟩

#print axioms direct_chosen_polynomial
#print axioms source_A2_direct_completed_slot
#print axioms source_A2_direct_actual_one_query
end
end A2R45Literal
