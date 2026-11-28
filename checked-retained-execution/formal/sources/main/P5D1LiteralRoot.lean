import P5D1LiteralOldRows
import J6R12BlueprintReach

/-! One source root for the literal old-row E1/D1 instance. Its packing can
be fixed before the pin signs and is honoured by the exact R12 selector. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun J6R12Blueprint
  P11FullPacking Paper5.HybridClosure J1MainSourceCollision

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
local notation "N" => dNetwork F cubic

noncomputable def oldRowRoot (f : ℤ[X]) (σ : W → Bool) : Call (PhysicalHost f 1) :=
  ⟨physicalHost N (oldRowFile F cubic f (4*Fintype.card W+1) σ),
    0, Fintype.card (DWire F), 4*Fintype.card W+1⟩

noncomputable abbrev oldRowSize : ℕ := Fintype.card (Clone W) + Fintype.card (ClauseIndex F)

include cubic in
theorem oldRow_size_exact :
    2*oldRowSize F=21*Fintype.card W := by
  have h := GraphCutMoments.weighted_incidence F (fun _ => (1:ℕ))
  have hdegree : F.card*2 = Fintype.card W*3 := by simpa [cubic] using h
  simp only [oldRowSize,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe]
  omega

theorem oldRowRoot_tags (f : ℤ[X]) (σ : W → Bool) :
    GoodTags (oldRowRoot F cubic f σ).host (oldRowRoot F cubic f σ).prec := by
  intro v
  change 4*Fintype.card W+1 ≤ 4*Fintype.card W+1
  exact le_rfl

theorem oldRowRoot_degree (f : ℤ[X]) (σ : W → Bool) {Δ : ℕ} (hΔ : 3 ≤ Δ) :
    GoodDegree (oldRowRoot F cubic f σ).host Δ := by
  constructor
  · intro v
    change Nat.card {e : DWire F // (dNetwork F cubic).row e = v} ≤ Δ
    let ϕ : {e : DWire F // (dNetwork F cubic).row e = v} ↪
        ↥(facFibre (dNetwork F cubic).row v) :=
      ⟨fun x => ⟨x.val, by simp [facFibre,x.property]⟩,
        fun _ _ h => Subtype.ext (congrArg (fun z : ↥(facFibre (dNetwork F cubic).row v) => z.val) h)⟩
    have hh : Nat.card {e : DWire F // (dNetwork F cubic).row e = v} ≤
        (facFibre (dNetwork F cubic).row v).card := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
        Fintype.card_le_of_injective ϕ ϕ.injective
    exact hh.trans ((d_old_degree F cubic v).trans hΔ)
  · intro v
    change Nat.card {e : DWire F // (dNetwork F cubic).col e = v} ≤ Δ
    let ϕ : {e : DWire F // (dNetwork F cubic).col e = v} ↪
        ↥(varFibre (dNetwork F cubic).col v) :=
      ⟨fun x => ⟨x.val, by simp [varFibre,x.property]⟩,
        fun _ _ h => Subtype.ext (congrArg (fun z : ↥(varFibre (dNetwork F cubic).col v) => z.val) h)⟩
    have hh : Nat.card {e : DWire F // (dNetwork F cubic).col e = v} ≤
        (varFibre (dNetwork F cubic).col v).card := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
        Fintype.card_le_of_injective ϕ ϕ.injective
    rw [d_subdivision_degree F cubic v] at hh
    omega

theorem oldRowRoot_stable (f : ℤ[X]) (σ : W → Bool)
    (hΔ : 3 ≤ J1PPrinted.sourceDelta (oldRowSize F)) :
    Stable (oldRowSize F) 3 (oldRowRoot F cubic f σ) := by
  refine stable_root _ _ _ rfl rfl (oldRowRoot_degree F cubic f σ hΔ)
    (oldRowRoot_tags F cubic f σ) ?_
  change Fintype.card (DWire F) ≤ 3*oldRowSize F
  rw [d_physical_wire_count F cubic]
  have hs := oldRow_size_exact F cubic
  omega

variable {f : ℤ[X]} {ell : ℕ}

/-- Generic pinned root for the same certified packing P. The source may
choose new legal layouts below the root; it may not relabel the chosen root. -/
noncomputable def sameRootSelector (S : Params (f:=f) (ell:=ell)) (Δ : ℕ)
    (root : Call (PhysicalHost f ell))
    (P : PhysicalPacking root.host.network (S.levelBits root.depth) (Fin 64)) :
    Selector S Δ := fun c d =>
  if h : c = root then h.symm ▸ P else defaultSelector S Δ c d

theorem sameRootSelector_pins (S : Params (f:=f) (ell:=ell)) (Δ : ℕ)
    (root : Call (PhysicalHost f ell))
    (P : PhysicalPacking root.host.network (S.levelBits root.depth) (Fin 64))
    (d : Ready S Δ root) :
    packing (sameRootSelector S Δ root P) d = P := by
  unfold packing sameRootSelector
  rw [dif_pos (show root = root from rfl)]

#print axioms oldRow_size_exact
#print axioms oldRowRoot_tags
#print axioms oldRowRoot_degree
#print axioms oldRowRoot_stable
#print axioms sameRootSelector_pins
end Paper5.D1Literal
