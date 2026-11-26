import P5D1LiteralPhysical
import P5D1LiteralRoot
import P5D1LiteralCount

/-! The fixed old-row root, with its declared graph-only physical
packing, receives its actual recursive children into the D1 field
expression, and the expression has the required integral count
residue. This is a source semantic statement, not a word-meter bound. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
  J6R12Blueprint J6R10Reachable J6R9Recursive P11FullPacking
  Paper5.HybridClosure J1PPrinted J6R12Integral

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}

local notation "N" => dNetwork F cubic
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r" σ => (oldRowRoot F cubic f σ)

set_option maxHeartbeats 18000000 in
theorem same_packing_printed_count
    (cfg : RootBounds (oldRowSize F) 3 f)
    (P : PhysicalPacking N ((S).levelBits 0) (Fin 64))
    (hΔ : 3 ≤ Δ) (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (σ : W → Bool) (ha : (S).cutoff < (r σ).edges) :
    let root := r σ
    let sel := sameRootSelector S Δ root P
    let PS := paddedShape (shape S Δ sel) (children S Δ sel) root
    let B := J6R12Blueprint.sourceBlueprint sel root hf
    ∃ (fit : ProofFit PS f root) (out : IntRing f 1),
      embed f 1 out =
        nativeFieldMenuSum PS f 1 root fit (fun w => B.program.run (B.program.child root w)) ∧
      reduce root.prec f 1 out =
        (PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F cubic)
          (MainClonedCNF.rightSlot F cubic) σ) : Residue f 1 root.prec) := by
  classical
  dsimp only
  let root := r σ
  let sel := sameRootSelector S Δ root P
  have hstable := oldRowRoot_stable F cubic f σ hΔ
  obtain ⟨fit,out,hfield,hd⟩ :=
    printed_physical_field_menu_integral cfg sel root hstable hf hF ha
  refine ⟨fit,out,hfield,?_⟩
  have he : reduce root.prec f 1 out = reduce root.prec f 1 (root.host.contract hf) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (reduce_zero_iff root.prec f hf 1 _).mpr hd
  rw [he]
  exact oldRow_contraction_reduce F cubic f hf root.prec σ

#print axioms same_packing_printed_count
end Paper5.D1Literal
