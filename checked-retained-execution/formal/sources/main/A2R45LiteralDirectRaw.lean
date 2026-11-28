import A2R45LiteralDirectRootRead
import A2R45LiteralAllModesNormalize

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10500000
set_option synthInstance.maxHeartbeats 170000
set_option maxRecDepth 2400
set_option linter.unusedSectionVars false

/-! The original allowed free-variable factor for the direct, one-
evaluation branch. This keeps the true occurrence path and removes only
declared unused variables, not optional auxiliary tautological switches. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial Std.Sat J7R9Compiler J6R11Blueprint J6R12Blueprint A1R43Literal

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V) (f : ℤ[X])

theorem direct_margins_of_printed_bounds (cfg : RootBounds (starSize (directM F)) 1 f) :
    PrintedMargins (directM F) := by
  apply printed_margins _ _ cfg.widthPos
  by_contra h
  have z : directM F=0 := Nat.eq_zero_of_not_pos h
  have t := cfg.constSmall
  change 1≤starSize (directM F) at t
  simp only [z,starSize,mul_zero] at t
  omega

local notation "G" => keepUsed F
local notation "m" => directM (G)
local notation "s" => starSize m

theorem source_A2_raw_direct_one_actual_slot (width : ∀ cl∈F,cl.length≤3)
    (cfg : RootBounds s 1 f) (hf : f.Monic)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    ∃ (guard : PrintedMargins m) (W : DirectPlan (G)),
      @zeroRead f s (directSelector (G) W f guard) (directRoot (G) W f)
        (direct_root_ready (G) W f (kept_width F width) guard cfg) (directNegative (G) W f guard) hf *
        2^Nat.card (Unused F)=PinnedCNF.modelCount F := by
  let guard := direct_margins_of_printed_bounds (G) f cfg
  obtain ⟨W,h⟩ := source_A2_direct_actual_one_query (G) f (kept_width F width) guard cfg hf
    (J6R12Bounds.positive_degree cfg) (all_kept_declared_variables_occur F)
  exact ⟨guard,W,(congrArg (fun q=>q*2^Nat.card (Unused F)) h).trans (keepUsed_count F).symm⟩

#print axioms direct_margins_of_printed_bounds
#print axioms source_A2_raw_direct_one_actual_slot
end
end A2R45Literal
