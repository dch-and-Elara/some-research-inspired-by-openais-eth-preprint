import P5HybridDOnlyTags
import P5HybridDOnlyScore

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000
set_option maxRecDepth 1900
set_option maxSynthPendingDepth 16

/-! The actual single rounded physical packing under both tags. -/
namespace Paper5.HybridDOnly
open scoped Classical BigOperators
open J1MainSourceCollision J6R10Repack J6R11CollisionReindex DiagonalAbundance P11FullPacking

section Pack
open J6R11Collision EmpiricalCutMoments
attribute [local irreducible] DiagonalAbundance.mean
variable {E A B U T : Type*} [Fintype E] [DecidableEq E]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T] {a : ℕ}

end Pack



section Pack
open J6R11Collision EmpiricalCutMoments
variable {E A B U T : Type*} [Fintype E] [DecidableEq E]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T] {a : ℕ}

theorem same_packing_with_both_ties (N : Network E A B)
    (exterior triangle : Fin a) (inner : A→Option U) (outer : A→Option T) (ν Δ : ℕ)
    (hcol : ∀ j,(varFibre N.col j).card≤2)
    (hrow : ∀ j,(facFibre N.row j).card≤3)
    (innerFib : ∀ j,(tagFibre (inner∘N.row) j).card≤3)
    (outerFib : ∀ j,(tagFibre (outer∘N.row) j).card≤2)
    (innerN : (tiedSlots (inner∘N.row)).card≤ν) (outerN : (tiedSlots (outer∘N.row)).card≤ν)
    (normal : 3*ν≤2*Nat.card E) (hΔ : 3≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E) :
    ∃ cfg : Atom A B (U⊕T) (Fin a)→Fin 64, ∃ P : PhysicalPacking N a (Fin 64),
      let tag := twoTags exterior triangle inner outer
      P.rowLabel=rowWord tag cfg ∧ P.colLabel=colWord cfg ∧
      P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)) ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤4*(Nat.card E:ℚ)+3*ν ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤2*(Nat.card E:ℚ)*Δ ∧
      Nat.card (Page a P.copies (Fin 64))*2^a≤3*Nat.card E ∧
      ∀ j g, Nat.card (rowsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*Nat.card E/64 ∧
             Nat.card (colsIn N (declaredGroup P.rowLabel P.colLabel j) g)≤3*Nat.card E/64 := by
  let tag := twoTags exterior triangle inner outer
  have bb := two_tie_dependent_pairs_le N.row N.col exterior triangle inner outer ν
    hcol hrow innerFib outerFib innerN outerN
  have bb' : ((dependentPairs tag N.row N.col).card:ℚ)≤4*(Nat.card E:ℚ)+3*ν := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast bb
  obtain ⟨cfg,dScore⟩ := chosen_cell_score_with_chart (S:=Fin 64) tag N.row N.col inferInstance
    (4*(Nat.card E:ℚ)+3*ν) bb'
  let f := varianceScore (declaredCell N (rowWord tag cfg) (colWord cfg))
  have actualCell : edgeCell N.row N.col (rowWord tag cfg,colWord cfg)=
      orderedCell tag N.row N.col cfg := rfl
  have actualScore := declared_variance_eq N (rowWord tag cfg,colWord cfg)
  rw [actualCell] at actualScore
  have exactScore : f≤4*(Nat.card E:ℚ)+3*ν := by
    change varianceScore (declaredCell N (rowWord tag cfg) (colWord cfg))≤_
    rw [actualScore]
    exact transport_deviation_chart _ _ dScore
  have hsix : 4*(Nat.card E:ℚ)+3*ν≤6*(Nat.card E:ℚ) := by
    have hq : 3*(ν:ℚ)≤2*(Nat.card E:ℚ) := by exact_mod_cast normal
    linarith only [hq]
  have standard : f≤2*(Nat.card E:ℚ)*Δ := by
    apply exactScore.trans (hsix.trans ?_)
    have hΔq : (3:ℚ)≤Δ := by exact_mod_cast hΔ
    have hq := mul_le_mul_of_nonneg_left hΔq (show 0≤2*(Nat.card E:ℚ) by positivity)
    linarith only [hq]
  obtain ⟨P,pr,pc,pp⟩ := actual_rounded_packing N (G:=Fin 64) (by simp)
    (rowWord tag cfg) (colWord cfg) Δ standard hcollision hslots
  refine ⟨cfg,P,pr,pc,?_,?_,?_,physical_packet_count P,physical_group_caps P (by simp)⟩
  · rwa [pr,pc]
  · rw [pr,pc]; exact exactScore
  · rw [pr,pc]; exact standard
end Pack

#print axioms same_packing_with_both_ties
end Paper5.HybridDOnly
