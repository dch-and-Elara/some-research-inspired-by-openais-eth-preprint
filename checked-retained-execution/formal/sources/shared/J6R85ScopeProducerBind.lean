import J6R85ScopeProducerAtlas
import J6R67UnifiedRateScope

/-! Exactly the R67/R79 input assembler for the same bank and machine.
In particular it no longer asks for a bound on the compiler's atlas
or a user-selected atlas-size parameter. -/
namespace J6R85ScopeProducer
open scoped Polynomial
open Polynomial J6R32StatefulArithmetic J6R24MeteredRecursion J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R30ProducedGateRegistry J6R51Online J6R50SourceProducer J6R57ScopeFee
open J6R67UnifiedRate J6R33StatefulArithmeticPage

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 14000000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (@Plan f ell s sel)

def measuredScopeWithPrintedAtlas
    (M : OnlineMachine T key prec tw bw page q) (B : PageBank f ell key prec tw bw page)
    (W : ScopeWordCaps) (fit : ScopeWordFits M B W) (code boot demand query words : ℕ)
    (hCode : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x),
      (sourceState M p w).input.code≤code)
    (hBoot : ∀ w : (P).Slot r,(M.initial w).steps≤boot)
    (hDemand : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x)
      (u : (P).Slot x) (w : (P).Slot ((P).child x u)),
      (M.demand (sourceState M p u) w).steps≤demand)
    (hQuery : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x)
      (u : (P).Slot x) (w : (P).Slot ((P).child x u)),
      sidecarQueryBill (M.demand (sourceState M p u) w).result≤query)
    (hWords : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x),
      measuredWordProducers (sourceState M p w).input≤words) :
    MeasuredScopeInputs M B := {
  wordCaps := W
  fit := fit
  bootBudget := boot
  demandBudget := demand
  queryBudget := query
  sourceWordBudget := words
  atlasSize := atlasSourceRoof s C r.prec ell page tw bw code
  boot := hBoot
  demand := hDemand
  query := hQuery
  sourceWords := hWords
  footprint := fun p w => same_online_occurrences_have_printed_atlas M code hCode p w }

#print axioms measuredScopeWithPrintedAtlas
end
end J6R85ScopeProducer
