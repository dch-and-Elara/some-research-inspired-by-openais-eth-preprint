import A2R45LiteralAllModesAdmit
import A2R45LiteralAllModesNormalize

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7300000
set_option synthInstance.maxHeartbeats 150000
set_option maxRecDepth 2250
set_option linter.unusedSectionVars false

/-! Original v9 A2 2331--2354 on raw inputs: pass to the actual cleaned,
used-variable CNF, use its same original literal chart and one supplied
all-mode value per printed address, and restore omitted variables. The
small nonempty threshold and machine-time costs are separate. -/
namespace A2R45Literal
open scoped Classical Polynomial BigOperators
open Polynomial Std.Sat J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R11Blueprint J6R12Blueprint J6R12Repack J7R9Compiler J1PPrinted J6R10Repack J6R11Repack

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V) (f : ℤ[X])
local notation "G" => normalizeSparse F
local notation "s" => sparseS (G)
local notation "c" => sparseRoot (G) f
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s

def rawSparseReady (notEmpty : ∀ cl∈F,0<cl.length)
    (width : ∀ cl∈F,cl.length≤3) (cfg : RootBounds s 12 f) :
    @J6R12Blueprint.Ready f 1 S Δ c :=
  normalized_sparse_ready (G) f (all_kept_declared_variables_occur _)
    (kept_nonempty _ (cleaned_nonempty F notEmpty))
    (kept_width _ (J7R9Clause.clean_width 3 width)) cfg

theorem source_raw_sparse_all_modes_one_table
    (notEmpty : ∀ cl∈F,0<cl.length)
    (width : ∀ cl∈F,cl.length≤3) (cfg : RootBounds s 12 f)
    (sel : Selector S Δ) (hf : f.Monic)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (oracle : WholeAnswers S f 1 c)
    (correct : ∀ t z, oracle t z=actualWhole sel (rawSparseReady F f notEmpty width cfg) hf t z) :
    let d := rawSparseReady F f notEmpty width cfg
    boxNatural f 1 (c).prec hf (wholeAssemble S f 1 c d.fit oracle) *
      2^Nat.card (Unused (J7R9Clause.clean F)) = PinnedCNF.modelCount F := by
  let k := 2^Nat.card (Unused (J7R9Clause.clean F))
  have read := source_sparse_all_modes_one_table (G) f
    (all_kept_declared_variables_occur _) (kept_nonempty _ (cleaned_nonempty F notEmpty))
    (kept_width _ (J7R9Clause.clean_width 3 width)) cfg sel hf oracle correct
  exact (congrArg (·*k) read).trans (normalizeSparse_count F).symm

theorem raw_cleanup_empty_counter (h : J7R9Clause.clean F=[]) :
    PinnedCNF.modelCount F=2^Fintype.card V := by
  rw [←J7R9Clause.clean_count F,h,raw_empty_list_power]

#print axioms rawSparseReady
#print axioms source_raw_sparse_all_modes_one_table
#print axioms raw_cleanup_empty_counter
end
end A2R45Literal
