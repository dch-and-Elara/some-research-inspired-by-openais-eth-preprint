import P5D1LiteralLedger

/-! Constructive finite visit ledger of the literal root products. The
value at each center/probe is the real finite grouped sample; no rational
field lift is computed by this loop. Counts still exclude lower-level and
bit-machine operations. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
variable (f : ℤ[X])
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r" σ => (oldRowRoot F cubic f σ)
local notation "r*" => (oldRowRoot F cubic f (fun _ => false))
variable (P : RootPacking F cubic f)

set_option maxHeartbeats 2400000 in
theorem siteLedger_actual_groupedSample
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3 ≤ Δ)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (d : Ready S Δ r*) (σ : W → Bool) (e : Ready S Δ (r σ))
    (t : PublicCenter F cubic f) (ζ : PublicProbe F cubic f) :
    let B := J6R12Blueprint.sourceBlueprint (rootSel F cubic f P σ) (r σ) hf
    groupedSample (eachShape F cubic f P σ) f 1 (r σ)
      (fun w => B.program.run (B.program.child (r σ) w)) t ζ =
      ((siteLedger F cubic f P d hf σ t ζ).map Prod.snd).sum := by
  classical
  dsimp only
  rw [siteLedger_value]
  let PS := eachShape F cubic f P σ
  let B := J6R12Blueprint.sourceBlueprint (rootSel F cubic f P σ) (r σ) hf
  let left (β : Terms PS (r σ) t) : Residue f 1 (registerPrecision S r* t) := ∏ g : Fin 64,
    B.program.run (B.program.child (r σ) ⟨t,ζ,β,g⟩)
  let right (β : PublicMenu F cubic f P d t) : Residue f 1 (registerPrecision S r* t) := ∏ g : Fin 64,
    publicReply F cubic f P d hf σ ⟨t,ζ,β,g⟩
  change (∑ β, left β) = ∑ β, right β
  refine Fintype.sum_equiv (publicMenuAtEquiv F cubic f P d σ e t) left right (fun β => ?_)
  apply Finset.prod_congr rfl
  intro g _
  exact printedReply_matches_public F cubic f P cfg hΔ hf hF d σ e ⟨t,ζ,β,g⟩

#print axioms siteLedger_actual_groupedSample
end Paper5.D1Literal
