import J6R11IntegralSites

/-! A valid-only family of actual physical calls fills the full grouped
source hypothesis. It changes neither the printed mode menu nor the
per-vertex creation precision; the only per-slot obligations are the
discrete mode and compiled-child identifications. -/
namespace J6R11Integral
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6ActiveRun

universe ur uc
variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ} {B : Blueprint S f ell}
variable {hf : f.Monic}

structure SiteDatum (B : Blueprint S f ell) (hf : f.Monic) (c : Call Host) where
  Row : Type ur
  Col : Type uc
  rowFinite : Fintype Row
  colFinite : Fintype Col
  network : Network (Fin c.edges) Row Col
  packing : PhysicalPacking network (S.levelBits c.depth) (Fin 64)
  file : EntryFile f ell network
  agrees :
    letI := rowFinite
    letI := colFinite
    ∀ x, (∏ v : Row ⊕ Col, (file v).frozen hf (assignment network x v)) =
      (B.entries c x).prod

variable {c : Call Host}

noncomputable def SiteDatum.toPlant (T : SiteDatum B hf c) : PlantedCall B c := by
  letI := T.rowFinite
  letI := T.colFinite
  exact PlantedCall.ofPhysical T.packing T.file hf T.agrees

structure PhysicalFamily (B : Blueprint S f ell) (hf : f.Monic) where
  Valid : Call Host → Prop
  childValid : ∀ c, Valid c → S.cutoff < c.edges → ∀ w, Valid (B.program.child c w)
  fit : ∀ c, Valid c → S.cutoff < c.edges → ProofFit S f c
  taper : ∀ c, Valid c → S.cutoff < c.edges →
    0 < S.levelWidth c.depth ∧ S.levelWidth c.depth ≤ c.edges
  bitFits : ∀ c, Valid c → S.cutoff < c.edges → S.levelWidth c.depth ≤ S.levelBits c.depth
  site : ∀ c, Valid c → S.cutoff < c.edges → SiteDatum B hf c
  modal : ∀ c (hc : Valid c) (ha : S.cutoff < c.edges) (t : Center S c),
    Modes S c t ≃ SiteMenu (site c hc ha).packing t (bitFits c hc ha)
  childMatches : ∀ c (hc : Valid c) (ha : S.cutoff < c.edges)
      (t : Center S c) (z : Probe S c) (β : Modes S c t) (g : Fin 64),
    let data := site c hc ha
    letI := data.rowFinite
    letI := data.colFinite
    B.expect (B.program.child c ⟨t,z,β,g⟩) =
      reduce (registerPrecision S c t) f ell
        (siteChild data.packing data.file hf (fit c hc ha) t z
          (bitFits c hc ha) (modal c hc ha t β) g)

noncomputable def PhysicalFamily.frozen (D : PhysicalFamily B hf) : FrozenLayout B where
  Valid := D.Valid
  child_valid := D.childValid
  fit := D.fit
  taper := D.taper
  active := fun c hc ha => (D.site c hc ha).toPlant

theorem PhysicalFamily.grouped (D : PhysicalFamily B hf) : D.frozen.ExactGrouped := by
  intro c hc ha t z
  let site := D.site c hc ha
  letI := site.rowFinite
  letI := site.colFinite
  have live := grouped_at_physical_site site.packing site.file hf (D.fit c hc ha) ha t z
    (D.bitFits c hc ha) (D.modal c hc ha t) (D.childMatches c hc ha t z)
  exact live

theorem PhysicalFamily.run_exact (D : PhysicalFamily B hf) (hd : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (c : Call Host) (hc : D.Valid c) :
    B.program.run c = reduce c.prec f ell (B.truth c) :=
  D.frozen.run_exact D.grouped hf hd c hc

#print axioms SiteDatum.toPlant
#print axioms PhysicalFamily.grouped
#print axioms PhysicalFamily.run_exact
end J6R11Integral
