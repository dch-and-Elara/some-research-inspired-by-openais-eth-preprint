import J6R79NumericCountercap

/-! Nonvacuity: the padding construction retains checked word-fit,
atlas fit and directory bounds, and every nonboot production budget.
Its only additional cost certificate is the measured extra boot steps. -/
namespace J6R79Numeric
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R50SourceProducer J6R51Online
open J6R55CachedLedger J6R57ScopeFee J6R67UnifiedRate

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4300

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Pg" => (PageBank f ell key prec tw bw page)
local notation "P" => (@Plan f ell s sel)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def padMeasuredScope {M : Machine} {B : Pg} (F : MeasuredScopeInputs M B) (extra : ℕ) :
    MeasuredScopeInputs (padInitialDebit M extra) B := by
  have hs {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x) :
      sourceState (padInitialDebit M extra) p w=sourceState M p w :=
    boot_fee_padding_keeps_all_real_source_states M extra p w
  refine
    { wordCaps := F.wordCaps
      fit := ⟨?_, ?_, ?_, F.fit.headers, ?_⟩
      bootBudget := F.bootBudget+extra
      demandBudget := F.demandBudget
      queryBudget := F.queryBudget
      sourceWordBudget := F.sourceWordBudget
      atlasSize := F.atlasSize
      boot := ?_
      demand := ?_
      query := ?_
      sourceWords := ?_
      footprint := ?_ }
  · intro x p w
    simpa only [borns, hs p w] using F.fit.entry p w
  · exact F.fit.boot
  · intro x p w
    rw [hs p w]
    exact F.fit.handles p w
  · intro x p u w
    change let D := (M.demand (sourceState (padInitialDebit M extra) p u) w).result.directory
      D.k1≤F.wordCaps.ownerKey ∧ D.k2≤F.wordCaps.seatKey ∧
        D.owners.length≤F.wordCaps.ownerRows ∧ D.seats.length≤F.wordCaps.seatRows
    rw [hs p u]
    exact F.fit.lookup p u w
  · intro w
    exact Nat.add_le_add_right (F.boot w) extra
  · intro x p u w
    change (M.demand (sourceState (padInitialDebit M extra) p u) w).steps ≤ F.demandBudget
    rw [hs p u]
    exact F.demand p u w
  · intro x p u w
    change sidecarQueryBill (M.demand (sourceState (padInitialDebit M extra) p u) w).result ≤ F.queryBudget
    rw [hs p u]
    exact F.query p u w
  · intro x p w
    rw [hs p w]
    exact F.sourceWords p w
  · intro x p w
    rw [hs p w]
    exact F.footprint p w

theorem actual_widths_do_not_bound_numeric_gate {M : Machine} {B : Pg}
    (F : MeasuredScopeInputs M B) (w : (P).Slot r) (target ptr fixed arithmetic : ℕ) :
    let F' := padMeasuredScope F (target+1)
    F'.wordCaps=F.wordCaps ∧ F'.atlasSize=F.atlasSize ∧
    F'.demandBudget=F.demandBudget ∧ F'.queryBudget=F.queryBudget ∧
    F'.sourceWordBudget=F.sourceWordBudget ∧
    (∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (u : (P).Slot x),
      sourceState (padInitialDebit M (target+1)) p u=sourceState M p u) ∧
    target<fixed+(arithmetic+measuredPerScope F' ptr) := by
  dsimp only
  refine ⟨rfl,rfl,rfl,rfl,rfl,boot_fee_padding_keeps_all_real_source_states M _ ,?_⟩
  have h := measuredScope_dominates_real_boot (padMeasuredScope F (target+1)) ptr w
  change (M.initial w).steps+(target+1)≤_ at h
  omega

#print axioms padMeasuredScope
#print axioms actual_widths_do_not_bound_numeric_gate
end
end J6R79Numeric
