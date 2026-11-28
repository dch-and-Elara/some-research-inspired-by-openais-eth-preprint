import J6R110ScopeWordRatesDimensions
import J6R110ScopeWordRatesQuery

/-! Discharge the two corresponding fields of the existing R67/R102
scope record on the selected actual state, with no alternate runner. -/
namespace J6R110ScopeWordRates
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R48RawRoute
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R49SourceLayout J6R50SourceProducer J6R51Online
open J6R52Dispatch J6R53Dispatch J6R54Dispatch J6R55Dispatch J6R55Public J6R54PublicFamily
open J6R57ScopeFee J6R68RateJoint J6R88ScopeCode J6R92NativeWidth J6R102NativeCodeMeter
open J6R10Repack J6R58BootScope

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000
set_option maxRecDepth 4600
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}

/-- The reference is to the actual existing resident table supplied to
the reader. `invokes` is equality of complete query meters, not addresses. -/
structure AlreadyInvokedKeyedQuery (I : Meter (FixedRequest X w)) (K N : ℕ) where
  addr : ℕ
  tape : List (RefRow addr (Word I.result.directory.k1×Word I.result.directory.k2×Bool))
  address : Port v.child.host.Edge→Word addr
  invokes : ∀ h,I.result.directory.queries h=readBootQueryRow tape (address h)
  addrWidth : addr≤K
  ownWidth : I.result.directory.k1≤K
  seatWidth : I.result.directory.k2≤K
  rows : tape.length≤N

variable (request : ∀ {t : Ticket sel r} (Y : StoredSite T t key prec tw bw page)
  (j : (Plan sel).Slot t.child),Meter (FixedRequest Y j))
variable (M : OnlineMachine T key prec tw bw page rate)

/-- Identifies the entire selected demand acquisition. Its outer fee
still includes the R102 roster scan, and is not bounded by this lemma. -/
def ActualR55R102Demand : Prop :=
  ∀ {t : Ticket sel r} (Y : StoredSite T t key prec tw bw page) (j : (Plan sel).Slot t.child),
    M.demand Y j=(meteredSelectedDemand (request Y j)).bind measureLocalLoad

theorem actual_selected_R55_R102_composes_through_the_demand_field :
    ActualR55R102Demand request (withPaidDemand (withSelectedDemands M request)) :=
  fun _ _=>rfl

def actualSidecarRoof (K N : ℕ) : ℕ := (2*K)*(locateFee K N+9*K+9)

/-- Both certified bounds use the actual current `sourceState` after the
actual selected demand. The first occurrence is still accounted by its
original root writer/issuer; the descendants use the R55 event. -/
theorem same_selected_machine_supplies_query_and_source_word_fields
    (selected : ActualR55R102Demand request M) (K N first : ℕ)
    (dimensions : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (Plan sel).Slot c)
      (j : (Plan sel).Slot ((Plan sel).child c u)), LiteralRequestSizes (request (sourceState M p u) j) K)
    (queries : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (Plan sel).Slot c)
      (j : (Plan sel).Slot ((Plan sel).child c u)),
      Nonempty (AlreadyInvokedKeyedQuery (request (sourceState M p u) j) K N))
    (firstWords : ∀ u : (Plan sel).Slot r,
      measuredWordProducers (sourceState M (Path.root : Path sel r r) u).input≤first) :
    (∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (Plan sel).Slot c)
      (j : (Plan sel).Slot ((Plan sel).child c u)),
      sidecarQueryBill (M.demand (sourceState M p u) j).result≤actualSidecarRoof K N) ∧
    (∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (Plan sel).Slot c),
      measuredWordProducers (sourceState M p u).input≤max first (descendantSourceWordsRoof K)) := by
  constructor
  · intro c p u j
    let Y := sourceState M p u
    obtain ⟨Q⟩ := queries p u j
    change sidecarQueryBill (M.demand Y j).result≤_
    rw [selected Y j]
    exact R102_selected_sidecar_query_from_the_actual_keyed_read (request Y j) Q.tape Q.address Q.invokes
      K N K Q.addrWidth Q.ownWidth Q.seatWidth Q.rows (dimensions p u j).edges
  · intro c p u
    cases p with
    | root => exact (firstWords u).trans (le_max_left _ _)
    | step p j =>
      let Y := sourceState M p j
      change measuredWordProducers (M.demand Y u).result.advance.next.input≤_
      rw [selected Y u]
      exact (selected_R102_descendant_words_are_bounded_by_literal_dimensions (request Y u)
        (dimensions p j u)).trans (le_max_right _ _)

end
#print axioms actual_selected_R55_R102_composes_through_the_demand_field
#print axioms same_selected_machine_supplies_query_and_source_word_fields
end J6R110ScopeWordRates