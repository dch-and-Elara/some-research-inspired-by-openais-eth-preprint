import J6R11IntegralParent
import J6R10IntegralCenter

/-! An active call's tensors may have distinct stored creation
precisions, and its page type may vary with the actual packing. This
is the frozen-tensor analogue of R10's finite parent-list SourceLayout.
Only genuinely valid active calls need to provide an atlas. -/
namespace J6R11Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Integral J6R10Repack
open J6ActiveRun J6ActiveSchedule J6ActiveUniqueness J6ActivePrintedHermite P1DyadicGrid

universe up
variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ} {B : Blueprint S f ell}

structure PlantedCall (B : Blueprint S f ell) (c : Call Host) where
  Page : Type up
  decidePage : DecidableEq Page
  atlas : Atlas (Fin c.edges) Page (S.levelBits c.depth)
  rowLift : (Fin c.edges → Bool) → IntRing f ell
  colLift : (Fin c.edges → Bool) → IntRing f ell
  agrees : ∀ x, rowLift x * colLift x = (B.entries c x).prod

variable {c : Call Host}

noncomputable def PlantedCall.deform (P : PlantedCall.{up} B c) : (RatRing f ell)[X] :=
  @globalNetwork (Fin c.edges) P.Page _ P.decidePage
    (S.levelBits c.depth) f ell P.atlas P.rowLift P.colLift

noncomputable def PlantedCall.jet (P : PlantedCall.{up} B c) (t : ℤ) : (IntRing f ell)[X] :=
  @integralNetwork (Fin c.edges) P.Page _ P.decidePage
    (S.levelBits c.depth) f ell P.atlas t P.rowLift P.colLift

theorem PlantedCall.degree (P : PlantedCall.{up} B c) :
    P.deform.natDegree ≤ J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth) := by
  letI : DecidableEq P.Page := P.decidePage
  simpa only [Fintype.card_fin] using network_degree f ell P.atlas P.rowLift P.colLift

theorem PlantedCall.integral (P : PlantedCall.{up} B c) (t : Center S c) :
    (P.jet t.val).map (embed f ell) =
      atNode (dyadicUnit (S.levelBits c.depth)) (t.val:RatRing f ell) P.deform := by
  letI : DecidableEq P.Page := P.decidePage
  exact network_embed f ell P.atlas (active_grid _ _ _ t.property).1 P.rowLift P.colLift

theorem PlantedCall.origin (P : PlantedCall.{up} B c) :
    P.deform.eval 0 = embed f ell (B.truth c) := by
  letI : DecidableEq P.Page := P.decidePage
  unfold PlantedCall.deform
  rw [network_origin,Blueprint.truth]
  congr 1
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun x _ => ?_)
  exact P.agrees x

noncomputable def PlantedCall.ofPhysical {A B₀ G : Type*}
    [Fintype A] [Fintype B₀] [LinearOrder G] [Fintype G]
    {N : Network (Fin c.edges) A B₀} (P : PhysicalPacking N (S.levelBits c.depth) G)
    (file : EntryFile f ell N) (hf : f.Monic)
    (agree : ∀ x, (∏ v : A ⊕ B₀, (file v).frozen hf (assignment N x v)) =
      (B.entries c x).prod) :
    PlantedCall B c where
  Page := P11FullPacking.Page (S.levelBits c.depth) P.copies G
  decidePage := inferInstance
  atlas := parentAtlas P
  rowLift := rowProduct N file hf
  colLift := colProduct N file hf
  agrees := fun x => (mixed_diagonal N file hf x).trans (agree x)

structure FrozenLayout (B : Blueprint S f ell) where
  Valid : Call Host → Prop
  child_valid : ∀ c, Valid c → S.cutoff < c.edges → ∀ w, Valid (B.program.child c w)
  fit : ∀ c, Valid c → S.cutoff < c.edges → ProofFit S f c
  taper : ∀ c, Valid c → S.cutoff < c.edges →
    0 < S.levelWidth c.depth ∧ S.levelWidth c.depth ≤ c.edges
  active : ∀ c, Valid c → S.cutoff < c.edges → PlantedCall.{up} B c

def FrozenLayout.ExactGrouped (D : FrozenLayout.{up} B) : Prop :=
  ∀ c (hc : D.Valid c) (ha : S.cutoff < c.edges) (t : Center S c) (z : Probe S c),
    groupedSample S f ell c (fun w => B.expect (B.program.child c w)) t z =
      (((D.active c hc ha).jet t.val).map (reduce (registerPrecision S c t) f ell)).eval
        (sampleNode S f ell c (D.fit c hc ha) t z)

noncomputable def FrozenLayout.sourceSpec (D : FrozenLayout.{up} B)
    (grouped : D.ExactGrouped) : B.SourceSpec := by
  classical
  exact {
    Valid := D.Valid
    child_valid := D.child_valid
    deformation := fun c =>
      if h : D.Valid c ∧ S.cutoff < c.edges then (D.active c h.1 h.2).deform else 0
    jets := fun c t =>
      if h : D.Valid c ∧ S.cutoff < c.edges then (D.active c h.1 h.2).jet t else 0
    fit := D.fit
    taper := D.taper
    degree := fun c hc ha => by
      rw [dif_pos ⟨hc,ha⟩]
      exact (D.active c hc ha).degree
    integral := fun c hc ha t => by
      rw [dif_pos ⟨hc,ha⟩,dif_pos ⟨hc,ha⟩]
      exact (D.active c hc ha).integral t
    origin := fun c hc ha => by
      rw [dif_pos ⟨hc,ha⟩]
      exact (D.active c hc ha).origin
    grouped := fun c hc ha t z => by
      rw [dif_pos ⟨hc,ha⟩]
      exact grouped c hc ha t z }

theorem FrozenLayout.run_exact (D : FrozenLayout.{up} B) (grouped : D.ExactGrouped)
    (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (c : Call Host) (hc : D.Valid c) :
    B.program.run c = reduce c.prec f ell (B.truth c) :=
  B.run_exact (D.sourceSpec grouped) hf hd c hc

#print axioms PlantedCall.degree
#print axioms PlantedCall.integral
#print axioms PlantedCall.origin
#print axioms PlantedCall.ofPhysical
#print axioms FrozenLayout.sourceSpec
#print axioms FrozenLayout.run_exact
end J6R11Integral
