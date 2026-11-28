import P5D1LiteralHostAgenda
import P5D1LiteralChain

/-! The actual recursive reply, at a common root address, equals the
frozen child contraction at the prescribed receiving precision. -/
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

noncomputable def publicReply (d : Ready S Δ r*) (hf : f.Monic) (σ : W → Bool)
    (a : PublicAddress F cubic f P d) : Residue f 1 (registerPrecision S r* a.1) :=
  reduce (registerPrecision S r* a.1) f 1 ((publicChildHost F cubic f P d σ a).contract hf)

theorem publicReply_local (d : Ready S Δ r*) (hf : f.Monic)
    (a : PublicAddress F cubic f P d) (σ τ : W → Bool)
    (h : ∀ v : PinSlice F cubic P (PublicIndex F cubic f d a.1) a.2.2.2,
      σ v.val = τ v.val) :
    publicReply F cubic f P d hf σ a = publicReply F cubic f P d hf τ a := by
  unfold publicReply
  rw [publicChildHost_local F cubic f P d a σ τ h]

set_option maxHeartbeats 18000000 in
theorem printedReply_matches_public
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3 ≤ Δ)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (d : Ready S Δ r*) (σ : W → Bool) (e : Ready S Δ (r σ))
    (w : let sel := rootSel F cubic f P σ
         Address (paddedShape (shape S Δ sel) (children S Δ sel) (r σ)) (r σ)) :
    let sel := rootSel F cubic f P σ
    let B := J6R12Blueprint.sourceBlueprint sel (r σ) hf
    B.program.run (B.program.child (r σ) w) =
      publicReply F cubic f P d hf σ (paddedRootAgendaEquiv F cubic f P σ d e w) := by
  classical
  dsimp only
  let root := r σ
  let sel := rootSel F cubic f P σ
  let B := J6R12Blueprint.sourceBlueprint sel root hf
  let child := B.program.child root w
  let D : B.SourceSpec := actualSourceSpec S Δ sel root
    (printedGuards cfg sel root (oldRowRoot_stable F cubic f σ hΔ)) hf
  have hc : D.Valid child := D.child_valid root (NativeReach.reflexive _) e.active w
  have hstable := stable_reachable cfg sel (show NativeReach (Plan sel) root child from hc)
    (oldRowRoot_stable F cubic f σ hΔ)
  change B.program.run child = _
  rw [B.run_exact D hf hF child hc, physicalBlueprint_truth hf B rfl child hstable.edgeCount]
  change reduce child.prec f 1 (child.host.contract hf) = _
  rw [show child.host =
      publicChildHost F cubic f P d σ (paddedRootAgendaEquiv F cubic f P σ d e w) from
    paddedChild_matches_public F cubic f P d σ e hf w]
  rfl

#print axioms publicReply_local
#print axioms printedReply_matches_public
end Paper5.D1Literal
