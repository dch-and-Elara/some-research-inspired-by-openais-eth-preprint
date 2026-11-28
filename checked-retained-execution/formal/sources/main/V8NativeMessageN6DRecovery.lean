import V8NativeMessageN6DTarget
import P5D1LiteralChain

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12000000

/-! The single exterior edge restriction also passes through the
already verified original recursive/field menu for the same real
four-copy file, not merely through the abstract graph count. -/
namespace V8NativeMessage.N6D
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
open J6R12Blueprint J6R10Reachable J6R9Recursive P11FullPacking J1PPrinted J6R12Integral
open Paper5.HybridClosure Paper5.D1Literal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀ v, GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "hF" => replaced_cubic E baseCubic loopless
local notation "N" => dNetwork F hF
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)

/-- This is only the one-pair restriction with all outside pins true.
The rank/list theorem still uses the exterior target, not the original
global CNF count on arbitrary multi-pair words. -/
theorem printed_origin_one_pair
    (cfg : RootBounds (oldRowSize F) 3 f)
    (P : PhysicalPacking N ((S).levelBits 0) (Fin 64))
    (hΔ : 3≤Δ) (hf : f.Monic) (hdegree : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (e : E) (x y : Bool)
    (active : (S).cutoff<(oldRowRoot F hF f (pairWord E baseCubic e x y)).edges) :
    let root := oldRowRoot F hF f (pairWord E baseCubic e x y)
    let sel := sameRootSelector S Δ root P
    let PS := paddedShape (shape S Δ sel) (children S Δ sel) root
    let B := J6R12Blueprint.sourceBlueprint sel root hf
    ∃ (fit : ProofFit PS f root) (out : IntRing f 1),
      embed f 1 out =
        nativeFieldMenuSum PS f 1 root fit (fun w => B.program.run (B.program.child root w)) ∧
      reduce root.prec f 1 out = orValue (Residue f 1 root.prec) x y := by
  dsimp only
  obtain ⟨fit,out,right,recovered⟩ := same_packing_printed_count F hF cfg P hΔ hf hdegree
    (pairWord E baseCubic e x y) active
  refine ⟨fit,out,right,recovered.trans ?_⟩
  rw [native_count_one_pair E baseCubic loopless e x y]
  cases x <;> cases y <;> simp [orValue]

#print axioms printed_origin_one_pair
end
end V8NativeMessage.N6D
