import P5EveryCollisionPacking
import P5GreedyExistence

namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6R12Blueprint
  P11FullPacking Paper5.HybridClosure J1PPrinted GraphCutMoments
open Paper5.HybridClosure.Printed (dLambda printedExponent)
variable {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]
variable (F : Finset (W × W)) (reg : ∀ v,degree F v=3) (f : ℤ[X])
local notation "N" => Fintype.card W
local notation "SP" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F reg f (fun _ => false))

/-- A complete source conditional-expectation trace for the labels carried
by this very packing. Padding and within-cell placement are unrestricted. -/
abbrev SourceTrace (P : RootPacking F reg f) : Prop :=
  Paper5.RootGreedy.Prefix (dNetwork F reg).row (dNetwork F reg).col
    (Sum.elim P.rowLabel P.colLabel) Finset.univ

omit [Nonempty W] in
theorem sourceTrace_collision (P : RootPacking F reg f) (hΔ : 3≤Δ)
    (h : SourceTrace F reg f P) : CollisionBound F reg f P := by
  apply Paper5.RootGreedy.every_full_transcript_collision (dNetwork F reg).row
    (dNetwork F reg).col Δ _ _ (Sum.elim P.rowLabel P.colLabel) h
  · intro v
    have he : J6R11Collision.fibre (dNetwork F reg).row v =
        J1MainSourceCollision.facFibre (dNetwork F reg).row v := by
      ext e; simp [J6R11Collision.fibre,J1MainSourceCollision.facFibre]
    rw [he]; exact (d_old_degree F reg v).trans hΔ
  · intro v
    have he : J6R11Collision.fibre (dNetwork F reg).col v =
        J1MainSourceCollision.varFibre (dNetwork F reg).col v := by
      ext e; simp [J6R11Collision.fibre,J1MainSourceCollision.varFibre]
    rw [he,d_subdivision_degree]; omega

omit [Nonempty W] in
theorem source_packing_exists (hΔ : 3≤Δ)
    (hn : 2*(J9PrintedSchedule.arrayCard ((SP).levelBits 0))^2*Δ≤Nat.card (DWire F))
    (hs : 2^((SP).levelBits 0)*J9PrintedSchedule.arrayCard ((SP).levelBits 0)≤Nat.card (DWire F)) :
    ∃ P : RootPacking F reg f, SourceTrace F reg f P ∧
      P.copies = ceilCopies (2^((SP).levelBits 0))
        (maxFiber (declaredCell (dNetwork F reg) P.rowLabel P.colLabel)) := by
  classical
  let Net := dNetwork F reg
  obtain ⟨z,tr⟩ := Paper5.RootGreedy.minimizing_transcript_exists
    (A:=Fin ((SP).levelBits 0)→Fin 64) Net.row Net.col Finset.univ
  let pair := J6R11CollisionGreedy.splitSample z
  have hv := Paper5.RootGreedy.every_full_transcript_collision Net.row Net.col Δ
    (fun v => by
      have e : J6R11Collision.fibre Net.row v=J1MainSourceCollision.facFibre Net.row v := by
        ext w; simp [J6R11Collision.fibre,J1MainSourceCollision.facFibre]
      rw [e]; exact (d_old_degree F reg v).trans hΔ)
    (fun v => by
      have e : J6R11Collision.fibre Net.col v=J1MainSourceCollision.varFibre Net.col v := by
        ext w; simp [J6R11Collision.fibre,J1MainSourceCollision.varFibre]
      rw [e,d_subdivision_degree]; omega) z tr
  obtain ⟨P,hrow,hcol,hcopies⟩ := actual_rounded_packing Net (by simp) pair.1 pair.2 Δ
    (by rw [J6R11CollisionReindex.declared_variance_eq Net pair,Nat.card_eq_fintype_card]; exact hv) hn hs
  refine ⟨P,?_,?_⟩
  · unfold SourceTrace
    rw [hrow,hcol]
    have same : Sum.elim pair.1 pair.2 = z := funext (fun x => by cases x <;> rfl)
    rw [same]; exact tr
  · rw [hrow,hcol]; exact hcopies

/-- The threshold depends only on the expansion parameter. The layout and
pin input stay universally quantified after the threshold has been chosen. -/
theorem eventual_every_printed_root (γ : ℚ) (hg : 0<γ) (hg₃ : γ≤3) :
    ∃ n₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
      (F : Finset (W × W)) (reg : ∀ v,degree F v=3) (_ : ∀ v,(v,v)∉F),
      n₀ ≤ Fintype.card W →
      (∀ U : Finset W, (γ/3)*(min U.card (Fintype.card W-U.card):ℕ)≤((boundary F U).card:ℚ)) →
      ∀ (f : ℤ[X]) (_ : f.natDegree=4*dLambda (Fintype.card W)) (hf : f.Monic)
        [Fact (Irreducible (NativeProbeRing.residuePoly f))] (P : RootPacking F reg f),
      SourceTrace F reg f P →
      ∃ d : Ready (printedParams (f:=f) (ell:=1) (oldRowSize F)) (sourceDelta (oldRowSize F))
          (oldRowRoot F reg f (fun _ => false)),
        2^(printedExponent γ (Fintype.card W)) ≤ Fintype.card (PublicSlot F reg f P d) ∧
        ∀ σ : W→Bool, 2^(printedExponent γ (Fintype.card W)) ≤
          (rootVisitLedger F reg f P d hf σ).length := by
  obtain ⟨n₀,hn⟩ := original_D1_size_threshold γ hg
  refine ⟨n₀,?_⟩
  intro W _ _ _ F reg loop hN expand f hdeg hf _ P trace
  obtain ⟨ready,size⟩ := hn _ hN
  have hΔ : 3≤sourceDelta (oldRowSize F) := by
    rw [oldRowSize_eq_dSize F reg]; exact ready.dDegree
  exact every_collision_packing_visits F reg f loop γ hg hg₃ expand ready size hdeg hf P
    (sourceTrace_collision F reg f P hΔ trace)

#print axioms sourceTrace_collision
#print axioms source_packing_exists
#print axioms eventual_every_printed_root
end Paper5.D1Literal
