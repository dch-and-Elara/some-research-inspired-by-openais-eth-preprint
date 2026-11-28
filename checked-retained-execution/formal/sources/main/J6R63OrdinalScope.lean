import J6R54PeakInputRunner

/-! Equality of accepted packet data, not equality of fees, is what
allows a ranked acquisition into the same scoped publisher. This
holds for the actual conditional publication and fallback branches. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R50SourceProducer J6R48RawRoute J6R51ParentFrames J6R51Online
open J6R52CacheWhole J6R54PeakInput
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3800
set_option maxHeartbeats 19000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Here" => (Path.root : Path sel r r)
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child}
variable {Out : Type}

theorem singular_scope_keeps_same_result_with_current_load
    (one prior : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ)
    (go old : (next : StoredSite T (successorTicket v u) key prec tw bw page)→
      ResidentBank next→SM L Out)
    (fallback : Meter Out) (bank : L) (words : one.result=prior.result)
    (agrees : ∀ next resident B,(go next resident B).result.1=(old next resident B).result.1) :
    (openBankDemandSingleEmission one cache retire go fallback bank).result=
      (openBankDemandSingleEmission prior cache retire old fallback bank).result := by
  simp only [single_local_emission_is_exactly_the_original_scoped_meter]
  unfold openBankDemand
  dsimp only
  rw [words]
  exact scope_return_congr _ _ _ _ _ _ (agrees _ _)

theorem same_first_scope_uses_ranked_continuation {w : (P).Slot r}
    (start : Meter (StoredSite T ((Here).ticket w) key prec tw bw page))
    (retire : J→ℕ)
    (go old : (next : StoredSite T ((Here).ticket w) key prec tw bw page)→ResidentBank next→SM L Out)
    (fallback : Meter Out) (bank : L)
    (agrees : ∀ next resident B,(go next resident B).result.1=(old next resident B).result.1) :
    (bootBankDemand start retire go fallback bank).result=
      (bootBankDemand start retire old fallback bank).result := by
  unfold bootBankDemand
  dsimp only
  exact scope_return_congr _ _ _ _ _ _ (agrees _ _)

#print axioms singular_scope_keeps_same_result_with_current_load
#print axioms same_first_scope_uses_ranked_continuation
end
end J6R63Ordinal
