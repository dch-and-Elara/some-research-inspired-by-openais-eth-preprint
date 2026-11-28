import P5EveryPrintedRoot
import P5D1LiteralPublicSum

/-! Join the public collision threshold, the native agenda's exact value
and the visit ledger on one and the same physical packing and root.
The resulting expense is still literal root visits, not a new bit-clock
or a bound on a different execution. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint
  J6R12Blueprint J6R9Recursive P11FullPacking Paper5.HybridClosure
  J1PPrinted GraphCutMoments
open Paper5.HybridClosure.Printed (dLambda printedExponent)

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 13000000
set_option maxRecDepth 4000

theorem eventual_collision_root_same_agenda_count_and_visits
    (γ : ℚ) (hg : 0<γ) (hg₃ : γ≤3) :
    ∃ n₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
      (F : Finset (W × W)) (reg : ∀ v,degree F v=3) (_ : ∀ v,(v,v)∉F),
      n₀ ≤ Fintype.card W →
      (∀ U : Finset W, (γ/3)*(min U.card (Fintype.card W-U.card):ℕ)≤((boundary F U).card:ℚ)) →
      ∀ (f : ℤ[X]) (_ : f.natDegree=4*dLambda (Fintype.card W)) (hf : f.Monic)
        [Fact (Irreducible (NativeProbeRing.residuePoly f))] (P : RootPacking F reg f),
      CollisionBound F reg f P →
      ∃ d : Ready (printedParams (f:=f) (ell:=1) (oldRowSize F)) (sourceDelta (oldRowSize F))
          (oldRowRoot F reg f (fun _ => false)),
        2^(printedExponent γ (Fintype.card W)) ≤ Fintype.card (PublicSlot F reg f P d) ∧
        ∀ σ : W→Bool,
          2^(printedExponent γ (Fintype.card W)) ≤ (rootVisitLedger F reg f P d hf σ).length ∧
          ∃ out : IntRing f 1, embed f 1 out=publicMenuSum F reg f P d hf σ ∧
            reduce (4*Fintype.card W+1) f 1 out =
              (PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
                (MainClonedCNF.rightSlot F reg) σ) : Residue f 1 (4*Fintype.card W+1)) := by
  obtain ⟨n₀,hn⟩ := original_D1_size_threshold γ hg
  refine ⟨n₀,?_⟩
  intro W _ _ _ F reg loop hN expand f hdeg hf _ P collision
  obtain ⟨ready,size⟩ := hn _ hN
  have hΔ : 3≤sourceDelta (oldRowSize F) := by
    rw [oldRowSize_eq_dSize F reg]
    exact ready.dDegree
  have hF : 0<f.natDegree := by
    have ho : 0<J9PrintedSchedule.rootU (dLambda (Fintype.card W)) := ready.dNodes
    unfold J9PrintedSchedule.rootU at ho
    omega
  let cfg := creating_source_config F reg f hdeg size
  obtain ⟨d,menu,visits⟩ :=
    every_collision_packing_visits F reg f loop γ hg hg₃ expand ready size hdeg hf P collision
  exact ⟨d,menu,fun σ=>⟨visits σ,common_agenda_field_count F reg f P cfg hΔ hf hF d σ⟩⟩

#print axioms eventual_collision_root_same_agenda_count_and_visits
end Paper5.D1Literal
