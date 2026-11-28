import J6R11IntegralStep
import J6R11IntegralFrozenRun

/-! One retained native centre/register may now fill the recursive
source obligation from literal finite children. The two remaining
interfaces are discrete: matching the scheduled mode address menu,
and matching the compiled child file and edge numbering. -/
namespace J6R11Integral
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking P1DyadicGrid J6ActiveRun J6ActiveSchedule
open J6R9Recursive J6R10Repack J6R10Integral J6R9PacketChild J6R9PacketScopes J6R10RowAffine

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ} {B : Blueprint S f ell}
variable {c : Call Host} {A C : Type*} [Fintype A] [Fintype C]
variable {N : Network (Fin c.edges) A C}

abbrev SiteMenu (P : PhysicalPacking N (S.levelBits c.depth) (Fin 64))
    (t : Center S c) (hu : S.levelWidth c.depth ≤ S.levelBits c.depth) :=
  ↥(J6RecursiveMenu.menu (registerPrecision S c t)
    (weight (bitOfCenter S c t hu) (registerPrecision S c t) P.mask))

noncomputable def siteChild (P : PhysicalPacking N (S.levelBits c.depth) (Fin 64))
    (file : EntryFile f ell N) (hf : f.Monic) (fit : ProofFit S f c)
    (t : Center S c) (z : Probe S c) (hu : S.levelWidth c.depth ≤ S.levelBits c.depth)
    (β : SiteMenu P t hu) (g : Fin 64) : IntRing f ell :=
  actualChildTruth P (bitOfCenter S c t hu) (active_grid _ _ _ t.property).2 rfl
    (registerPrecision S c t) (sampleNode S f ell c fit t z) file hf β.val g

theorem grouped_at_physical_site (P : PhysicalPacking N (S.levelBits c.depth) (Fin 64))
    (file : EntryFile f ell N) (hf : f.Monic) (fit : ProofFit S f c)
    (ha : S.cutoff < c.edges) (t : Center S c) (z : Probe S c)
    (hu : S.levelWidth c.depth ≤ S.levelBits c.depth)
    (modeEquiv : Modes S c t ≃ SiteMenu P t hu)
    (child_agree : ∀ β g,
      B.expect (B.program.child c ⟨t,z,β,g⟩) =
        reduce (registerPrecision S c t) f ell (siteChild P file hf fit t z hu (modeEquiv β) g)) :
    groupedSample S f ell c (fun w => B.expect (B.program.child c w)) t z =
      ((parentJet P file hf t.val).map (reduce (registerPrecision S c t) f ell)).eval
        (sampleNode S f ell c fit t z) := by
  classical
  let i := bitOfCenter S c t hu
  let p := registerPrecision S c t
  have ht := active_grid _ _ _ t.property
  have hstep := native_finite_step P i ht.1 ht.2 rfl p (register_positive S c t ha)
    (sampleNode S f ell c fit t z) file hf
  rw [hstep]
  unfold groupedSample
  conv_rhs => rw [← Finset.sum_coe_sort]
  let a' (β : Modes S c t) : Box f ell p :=
    ∏ g : Fin 64, B.expect (B.program.child c ⟨t,z,β,g⟩)
  let b' (β : SiteMenu P t hu) : Box f ell p :=
    ∏ g : Fin 64, reduce p f ell (siteChild P file hf fit t z hu β g)
  refine Fintype.sum_equiv modeEquiv a' b' (fun β => ?_)
  refine Finset.prod_congr rfl (fun g _ => ?_)
  exact child_agree β g

#print axioms siteChild
#print axioms grouped_at_physical_site
end J6R11Integral
