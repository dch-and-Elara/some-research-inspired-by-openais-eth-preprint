import J6R68ActiveInputsSweepEntries

/-! Coverage of the whole original residue field for the exact
Prepared paths. This changes neither the active centre's printed
probe count nor the existing Fin-indexed reader. -/
namespace J6R110CanonicalCoverage
open scoped Polynomial
open Polynomial AOracleMachineTime J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R49DFS
open J6R58ActivePrep J6R62ActivePrep J6R68ActiveInputs.Sweep

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 15000000
set_option maxRecDepth 4000

def fullProbeDegree (e : ℕ) : ℕ := 2^e-1

theorem full_probe_count (e : ℕ) : fullProbeDegree e+1=2^e :=
  Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity : 0 < (2:ℕ)^e))

theorem full_probe_fit (e : ℕ) : fullProbeDegree e+1≤2^e :=
  (full_probe_count e).le

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

include T in
/-- A Ready at a genuinely reachable active call already proves the
needed capacity in the same field used by the original Prepared. -/
theorem every_active_original_call_fits_the_full_chart
    {x : Call (PhysicalHost f ell)} (p : J6R32StatefulArithmetic.Path sel r x) (on : (S).cutoff<x.edges) :
    physicalProbeCount f ell s x≤fullProbeDegree f.natDegree+1 :=
  (readyAtPath T p on).fit.trans_eq (full_probe_count f.natDegree).symm

/-- Uses the existing R58 copy/scan at the original local ordinal;
a larger prepared table does not increase the number of calls. -/
theorem full_chart_serves_the_unchanged_original_probe_index
    (B : MaskTable f.natDegree (fullProbeDegree f.natDegree+1) (full_probe_fit f.natDegree))
    (p : J6R32StatefulArithmetic.Path sel r c) (on : (S).cutoff<c.edges) (i : Probe S c) :
    let n := physicalProbeCount f ell s c
    let fit : n≤2^f.natDegree := (readyAtPath T p on).fit
    B.readRaw (every_active_original_call_fits_the_full_chart T p on) i=
      ⟨List.ofFn (NativeProbeRing.chosenRep f.natDegree n fit i),(i.val+1)*(3*f.natDegree+5)⟩ ∧
    i.val+1≤n := by
  exact ⟨MaskTable.read_raw_exact B _ i,Nat.succ_le_of_lt i.isLt⟩

#print axioms full_probe_count
#print axioms every_active_original_call_fits_the_full_chart
#print axioms full_chart_serves_the_unchanged_original_probe_index
end
end J6R110CanonicalCoverage
