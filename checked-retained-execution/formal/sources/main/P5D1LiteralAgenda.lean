import P5D1LiteralRoot
import P5D1LiteralLocality
import J6R12IntegralClosedCore

/-! The D1 menu carrier and its exact reindexing from the padded R12
recursive executor. Changing signs or choosing a later flattening
does not relabel a center, probe, or legal weighted mode. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
variable (f : ℤ[X])
local notation "N" => dNetwork F cubic
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r" σ => (oldRowRoot F cubic f σ)
local notation "r*" => (oldRowRoot F cubic f (fun _ => false))

noncomputable abbrev RootPacking := PhysicalPacking N ((S).levelBits 0) (Fin 64)

variable (P : RootPacking F cubic f)

noncomputable abbrev rootSel (σ : W → Bool) : Selector S Δ :=
  sameRootSelector S Δ (r σ) P

noncomputable abbrev PublicCenter := Center S r*
noncomputable abbrev PublicProbe := Probe S r*

noncomputable def PublicIndex (d : Ready S Δ r*) (t : PublicCenter F cubic f) :
    Fin ((S).levelBits 0) := centerIndex d t

noncomputable abbrev PublicMenu (d : Ready S Δ r*) (t : PublicCenter F cubic f) :=
  ↥(J6RecursiveMenu.menu (registerPrecision S r* t)
    (J6R10RowAffine.weight (PublicIndex F cubic f d t) (registerPrecision S r* t) P.mask))

noncomputable abbrev PublicSlot (d : Ready S Δ r*) :=
  Σ t : PublicCenter F cubic f, PublicProbe F cubic f × PublicMenu F cubic f P d t

/-- The dummy sign in d only witnesses graph/size readiness; it is not a
measured pin word and is absent from the menu definitions. -/
noncomputable abbrev PublicAddress (d : Ready S Δ r*) :=
  Σ t : PublicCenter F cubic f, PublicProbe F cubic f × PublicMenu F cubic f P d t × Fin 64

theorem root_literalMenu_eq (σ : W → Bool) (d : Ready S Δ r*) (e : Ready S Δ (r σ))
    (t : PublicCenter F cubic f) :
    LiteralMenu (rootSel F cubic f P σ) e t = PublicMenu F cubic f P d t := by
  have hp : packing (rootSel F cubic f P σ) e = P := sameRootSelector_pins S Δ (r σ) P e
  change ↥(J6RecursiveMenu.menu (registerPrecision S (r σ) t)
    (J6R10RowAffine.weight (centerIndex e t) (registerPrecision S (r σ) t)
      (packing (rootSel F cubic f P σ) e).mask)) = _
  rw [hp]
  rfl

/-- Exact coordinatewise menu transport: a weight or degree zero test
never deletes a legal root slot during the address reindex. -/
noncomputable def nativeRootAgendaEquiv (σ : W → Bool) (d : Ready S Δ r*)
    (e : Ready S Δ (r σ)) :
    NativeAddress (shape S Δ (rootSel F cubic f P σ)) (r σ) ≃ PublicAddress F cubic f P d :=
  Equiv.sigmaCongrRight (fun t : PublicCenter F cubic f =>
    (Equiv.refl (PublicProbe F cubic f)).prodCongr
      (((siteMenuEquiv (rootSel F cubic f P σ) e t).trans
        (Equiv.cast (root_literalMenu_eq F cubic f P σ d e t))).prodCongr
        (Equiv.refl (Fin 64))))

theorem nativeRootAgenda_indices (σ : W → Bool) (d : Ready S Δ r*)
    (e : Ready S Δ (r σ)) (w : NativeAddress (shape S Δ (rootSel F cubic f P σ)) (r σ)) :
    let q := nativeRootAgendaEquiv F cubic f P σ d e w
    q.1 = w.1 ∧ q.2.1 = w.2.1 ∧ q.2.2.2 = w.2.2.2 :=
  ⟨rfl,rfl,rfl⟩

/-- Padded top-level addresses are in bijection with the literal
occurrences indexed by the same public P, t, zeta, beta and group. -/
noncomputable def paddedRootAgendaEquiv (σ : W → Bool) (d : Ready S Δ r*)
    (e : Ready S Δ (r σ)) :
    let sel := rootSel F cubic f P σ
    let sh := shape S Δ sel
    let ch := children S Δ sel
    Address (paddedShape sh ch (r σ)) (r σ) ≃ PublicAddress F cubic f P d := by
  classical
  dsimp only
  let sel := rootSel F cubic f P σ
  let sh := shape S Δ sel
  let ch := children S Δ sel
  exact (nativeAddressEquiv sh ch (r σ) (r σ) (NativeReach.reflexive _)
    e.active (fun _ _ => weightAt_pos S Δ sel _ _ _)).symm.trans
      (nativeRootAgendaEquiv F cubic f P σ d e)

theorem paddedRootAgenda_indices (σ : W → Bool) (d : Ready S Δ r*)
    (e : Ready S Δ (r σ))
    (w : let sel := rootSel F cubic f P σ
         Address (paddedShape (shape S Δ sel) (children S Δ sel) (r σ)) (r σ)) :
    let q := paddedRootAgendaEquiv F cubic f P σ d e w
    q.1 = w.t ∧ q.2.1 = w.zeta ∧ q.2.2.2 = w.group := by
  classical
  let sel := rootSel F cubic f P σ
  let sh := shape S Δ sel
  let ch := children S Δ sel
  let E := nativeAddressEquiv sh ch (r σ) (r σ) (NativeReach.reflexive _)
    e.active (fun _ _ => weightAt_pos S Δ sel _ _ _)
  have h := address_indices sh ch (r σ) (r σ) (NativeReach.reflexive _) e.active
    (fun _ _ => weightAt_pos S Δ sel _ _ _) (E.symm w)
  change (E (E.symm w)).t = (E.symm w).1 ∧ (E (E.symm w)).zeta = (E.symm w).2.1 ∧
    (E (E.symm w)).group = (E.symm w).2.2.2 at h
  rw [E.apply_symm_apply] at h
  exact ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩

#print axioms root_literalMenu_eq
#print axioms nativeRootAgendaEquiv
#print axioms nativeRootAgenda_indices
#print axioms paddedRootAgendaEquiv
#print axioms paddedRootAgenda_indices
end Paper5.D1Literal
