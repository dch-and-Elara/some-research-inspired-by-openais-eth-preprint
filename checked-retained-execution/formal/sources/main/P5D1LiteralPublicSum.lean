import P5D1LiteralResponse

/-! Fixed public agenda, fixed actual decoder weights, and a common
whole function of every sign input on the same E1 packing. -/
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

noncomputable abbrev eachShape (σ : W → Bool) :=
  let sel := rootSel F cubic f P σ
  paddedShape (shape S Δ sel) (children S Δ sel) (r σ)

noncomputable def publicMenuAtEquiv (d : Ready S Δ r*) (σ : W → Bool) (e : Ready S Δ (r σ))
    (t : PublicCenter F cubic f) :
    Terms (eachShape F cubic f P σ) (r σ) t ≃ PublicMenu F cubic f P d t := by
  let sel := rootSel F cubic f P σ
  let sh := shape S Δ sel
  let ch := children S Δ sel
  exact ((nativeSlotEquiv sh ch (r σ) (r σ) (NativeReach.reflexive _) e.active t
     (weightAt_pos S Δ sel _ _)).symm.trans (siteMenuEquiv sel e t)).trans
       (Equiv.cast (root_literalMenu_eq F cubic f P σ d e t))

theorem eachAddress_apply_public (d : Ready S Δ r*) (σ : W → Bool) (e : Ready S Δ (r σ))
    (t : PublicCenter F cubic f) (ζ : PublicProbe F cubic f)
    (β : Terms (eachShape F cubic f P σ) (r σ) t) (g : Fin 64) :
    paddedRootAgendaEquiv F cubic f P σ d e ⟨t,ζ,β,g⟩ =
      ⟨t,ζ,publicMenuAtEquiv F cubic f P d σ e t β,g⟩ := rfl

noncomputable def publicMenuWeight (d : Ready S Δ r*) (t : PublicCenter F cubic f)
    (ζ : PublicProbe F cubic f) : RatRing f 1 := fieldMenuWeight S f 1 r* d.fit t ζ

theorem eachWeight_eq_public (d : Ready S Δ r*) (σ : W → Bool)
    (fit : ProofFit (eachShape F cubic f P σ) f (r σ))
    (t : PublicCenter F cubic f) (ζ : PublicProbe F cubic f) :
    fieldMenuWeight (eachShape F cubic f P σ) f 1 (r σ) fit t ζ =
      publicMenuWeight F cubic f d t ζ := rfl

noncomputable def publicTerm (d : Ready S Δ r*) (hf : f.Monic) (σ : W → Bool)
    (u : PublicSlot F cubic f P d) : RatRing f 1 :=
  publicMenuWeight F cubic f d u.1 u.2.1 *
    ∏ g : Fin 64, embed f 1 (representative (registerPrecision S r* u.1) f 1
      (publicReply F cubic f P d hf σ ⟨u.1,u.2.1,u.2.2,g⟩))

noncomputable def publicMenuSum (d : Ready S Δ r*) (hf : f.Monic) (σ : W → Bool) : RatRing f 1 :=
  ∑ t : PublicCenter F cubic f, ∑ ζ : PublicProbe F cubic f, ∑ β : PublicMenu F cubic f P d t,
    publicTerm F cubic f P d hf σ ⟨t,ζ,β⟩

set_option maxHeartbeats 19000000 in
theorem eachMenuSum_eq_public (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3 ≤ Δ)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (d : Ready S Δ r*) (σ : W → Bool) (e : Ready S Δ (r σ))
    (fit : ProofFit (eachShape F cubic f P σ) f (r σ)) :
    let B := J6R12Blueprint.sourceBlueprint (rootSel F cubic f P σ) (r σ) hf
    nativeFieldMenuSum (eachShape F cubic f P σ) f 1 (r σ) fit
      (fun w => B.program.run (B.program.child (r σ) w)) =
        publicMenuSum F cubic f P d hf σ := by
  classical
  dsimp only
  let PS := eachShape F cubic f P σ
  let B := J6R12Blueprint.sourceBlueprint (rootSel F cubic f P σ) (r σ) hf
  unfold nativeFieldMenuSum publicMenuSum
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro ζ _
  let left (β : Terms PS (r σ) t) :=
    fieldMenuWeight PS f 1 (r σ) fit t ζ *
      ∏ g : Fin 64, embed f 1 (representative (registerPrecision S r* t) f 1
        (B.program.run (B.program.child (r σ) ⟨t,ζ,β,g⟩)))
  let right (β : PublicMenu F cubic f P d t) :=
    publicTerm F cubic f P d hf σ ⟨t,ζ,β⟩
  change (∑ β, left β) = ∑ β, right β
  refine Fintype.sum_equiv (publicMenuAtEquiv F cubic f P d σ e t) left right (fun β => ?_)
  unfold left right publicTerm
  rw [eachWeight_eq_public F cubic f P d σ fit t ζ]
  apply congrArg (fun z => publicMenuWeight F cubic f d t ζ * z)
  apply Finset.prod_congr rfl
  intro g _
  apply congrArg (fun x => embed f 1 (representative (registerPrecision S r* t) f 1 x))
  exact printedReply_matches_public F cubic f P cfg hΔ hf hF d σ e ⟨t,ζ,β,g⟩

set_option maxHeartbeats 9500000 in
/-- Faithful D1 representation for all sign words on one graph-only P:
the unreduced field expression uses exactly one fixed term per address
and receives the true model count. No runtime event is inferred. -/
theorem common_agenda_field_count (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3 ≤ Δ)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (d : Ready S Δ r*) (σ : W → Bool) :
    ∃ out : IntRing f 1, embed f 1 out = publicMenuSum F cubic f P d hf σ ∧
      reduce (4*Fintype.card W+1) f 1 out =
        (PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F cubic)
          (MainClonedCNF.rightSlot F cubic) σ) : Residue f 1 (4*Fintype.card W+1)) := by
  classical
  have ha : (S).cutoff < (r σ).edges := d.active
  let e := getReady cfg (oldRowRoot_stable F cubic f σ hΔ) ha
  obtain ⟨fit,out,hfield,hcount⟩ := same_packing_printed_count F cubic cfg P hΔ hf hF σ ha
  exact ⟨out,hfield.trans (eachMenuSum_eq_public F cubic f P cfg hΔ hf hF d σ e fit),hcount⟩

#print axioms publicMenuAtEquiv
#print axioms eachAddress_apply_public
#print axioms eachWeight_eq_public
#print axioms eachMenuSum_eq_public
#print axioms common_agenda_field_count
end Paper5.D1Literal
