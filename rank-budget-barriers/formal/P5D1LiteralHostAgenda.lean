import P5D1LiteralAgenda

/-! The exact generated child at each common root address. This joins
literal group sign locality to the real padded program's child factory,
not just to an isomorphic isolated graph. -/
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

noncomputable def publicChildHost (d : Ready S Δ r*) (σ : W → Bool)
    (a : PublicAddress F cubic f P d) : PhysicalHost f 1 :=
  let p := registerPrecision S r* a.1
  actualPacketHost P (PublicIndex F cubic f d a.1) (centerNonzero a.1) rfl
    p (J6R10Integral.box_two_nil p f 1) (sampleNode S f 1 r* d.fit a.1 a.2.1)
    (r σ).host.file a.2.2.1.val a.2.2.2

theorem publicChildHost_local (d : Ready S Δ r*) (a : PublicAddress F cubic f P d)
    (σ τ : W → Bool)
    (h : ∀ v : PinSlice F cubic P (PublicIndex F cubic f d a.1) a.2.2.2,
      σ v.val = τ v.val) :
    publicChildHost F cubic f P d σ a = publicChildHost F cubic f P d τ a := by
  unfold publicChildHost
  exact oldRow_child_group_local F cubic _ P _ _ _ _ _ _ _ _ _ _ h

private theorem publicChild_menu_transport (Q : RootPacking F cubic f) (h : Q=P)
    (d : Ready S Δ r*) (σ : W → Bool) (t : PublicCenter F cubic f) (z : PublicProbe F cubic f)
    (g : Fin 64) (β : PublicMenu F cubic f Q d t) :
    publicChildHost F cubic f Q d σ ⟨t,z,β,g⟩ =
      publicChildHost F cubic f P d σ
        ⟨t,z,(Equiv.cast (congrArg (fun X => PublicMenu F cubic f X d t) h)) β,g⟩ := by
  cases h
  rfl

set_option maxHeartbeats 5000000 in
theorem nativeChild_matches_public (d : Ready S Δ r*) (σ : W → Bool) (e : Ready S Δ (r σ))
    (w : NativeAddress (shape S Δ (rootSel F cubic f P σ)) (r σ)) :
    let sel := rootSel F cubic f P σ
    ((nativePlan (shape S Δ sel) (children S Δ sel)).child (r σ) ⟨w,e.active⟩).host =
      publicChildHost F cubic f P d σ (nativeRootAgendaEquiv F cubic f P σ d e w) := by
  dsimp only
  let sel := rootSel F cubic f P σ
  let Q : RootPacking F cubic f := packing sel e
  let m := siteMenuEquiv sel e w.1 w.2.2.1
  have hm : m.val = siteTuple sel e w := siteMenuEquiv_tuple sel e w.1 w.2.1 w.2.2.1 w.2.2.2
  have hp : Q = P := sameRootSelector_pins S Δ (r σ) P e
  have hc := congrArg Call.host (child_exact sel e w)
  exact hc.trans <| (congrArg (fun b => packetOfSite sel e w.1 w.2.1 b w.2.2.2) hm.symm).trans
    (publicChild_menu_transport F cubic f P Q hp d σ w.1 w.2.1 w.2.2.2 m)

set_option maxHeartbeats 7000000 in
theorem paddedChild_matches_public (d : Ready S Δ r*) (σ : W → Bool) (e : Ready S Δ (r σ))
    (hf : f.Monic)
    (w : let sel := rootSel F cubic f P σ
         Address (paddedShape (shape S Δ sel) (children S Δ sel) (r σ)) (r σ)) :
    let sel := rootSel F cubic f P σ
    let B := J6R12Blueprint.sourceBlueprint sel (r σ) hf
    (B.program.child (r σ) w).host =
      publicChildHost F cubic f P d σ (paddedRootAgendaEquiv F cubic f P σ d e w) := by
  classical
  dsimp only
  let sel := rootSel F cubic f P σ
  let NS := shape S Δ sel
  let NC := children S Δ sel
  let hreach : IsNative NS NC (r σ) (r σ) := NativeReach.reflexive _
  let positive := positive_at_native sel (r σ)
  rw [show (J6R12Blueprint.sourceBlueprint sel (r σ) hf).program.child (r σ) w =
      widenedChild NS NC (r σ) (r σ) hreach e.active (positive _ hreach e.active) w from
    paddedBlueprint_child NS NC (r σ) positive f 1 (physicalEntries hf) (r σ) hreach e.active w]
  exact nativeChild_matches_public F cubic f P d σ e _

#print axioms publicChildHost_local
#print axioms nativeChild_matches_public
#print axioms paddedChild_matches_public
end Paper5.D1Literal
