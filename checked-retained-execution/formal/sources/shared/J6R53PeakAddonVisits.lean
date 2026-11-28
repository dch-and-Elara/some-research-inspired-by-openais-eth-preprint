import J6R53PeakAddonBoot
import J6R53PeakAddonPath
import J6R52PeakCachedPhase
import J6R52PeakMode

/-! The reserve uses the same installed object that is passed to the
actual successful child, both first and at arbitrary later paths.
This is proof-side trace data, not a stack added to the evaluator. -/
namespace J6R53PeakAddon
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R16ModeCost J6R36ChildFramedRoute J6R41StructuredAllPaths J6R48RawRoute J6R50SourceProducer
open J6R51Peak J6R51Online J6R51ParentFrames J6R52Peak J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 3850
set_option maxHeartbeats 21000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def cachedReadAt (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) →
    ActiveChild (sel:=sel) (d:=ready_reachable cfg sel p.reached T.rootStable a) T.bank
  | _, .root,a => exteriorCachedRead M retire initial a
  | _, .step p w,a => sourceCachedRead M retire initial p w a

def cacheVisitAt (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) →
    Meter (Block (T.frame p.reached) ell × L)
  | _, .root => runCachedRoot M retire initial
  | _, .step p w => runCachedAfter M retire _ p w (sourceState M p w)
      (sourceBankAt M p w).result (stackBank (borns M) initial (.step p w))

def installedAddonDebit (M : OnlineMachine T key prec tw bw page q) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (w : (P).Slot x) → ℕ
  | _, .root,w => (M.initial w).steps+(sourceBankAt M .root w).steps
  | _, .step prev u,w => paidAcquisition (M.demand (sourceState M prev u) w)

theorem exact_scoped_read_uses_the_counted_child_bank
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let j := (borns M p w).job
    let out := cacheVisitAt M retire initial (.step p w)
    cachedReadAt M retire initial p a t z β g=
      ⟨out.result.1,installedAddonDebit M p w+
        (publishFee (stackBank (borns M) initial p) j.entry j.offset j.built+out.steps+retire j+4)⟩ := by
  cases p with
  | root =>
    have first := (actual_first_read_passes_and_pays_the_same_installed_addon_bank
      M retire initial legal a t z β g).1
    simp only [cachedReadAt,cacheVisitAt,installedAddonDebit,stackBank,borns,sourceState,sourceBankAt] at first ⊢
    rw [first]
    congr 1
    ac_rfl
  | step prev u =>
    have next := exact_cached_source_read_has_the_next_native_cache_bank M retire initial legal
      prev u a t z β g
    simpa only [cachedReadAt,cacheVisitAt,installedAddonDebit,stackBank,borns,sourceState,sourceBankAt] using next

def PaidBankVisit (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (p : Path sel r c) (w : (P).Slot c) : Prop :=
    let j := (borns M p w).job
    let out := cacheVisitAt M retire initial (.step p w)
    cachedReadAt M retire initial p w.property w.val.1 w.val.2.1 w.val.2.2.1 w.val.2.2.2=
      ⟨out.result.1,installedAddonDebit M p w+
        (publishFee (stackBank (borns M) initial p) j.entry j.offset j.built+out.steps+retire j+4)⟩

theorem every_legal_paid_occurrence_uses_its_physical_bank
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial)
    (p : Path sel r c) (w : (P).Slot c) :
    PaidBankVisit M retire initial p w ∧
      (sourceBankAt M p w).result.rows.length=2*c.edges := by
  have same := slot_is_literal_online_address (T:=T) p w
  have charged := exact_scoped_read_uses_the_counted_child_bank M retire initial legal p
    w.property w.val.1 w.val.2.1 w.val.2.2.1 w.val.2.2.2
  dsimp only at same charged
  refine ⟨?_,true_resident_bank_rows (sourceBankAt M p w).result⟩
  simpa only [PaidBankVisit,←same] using charged

inductive ObservedBankPath (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) : {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → Prop where
  | root : ObservedBankPath M retire initial (.root : Path sel r r) 0
  | visit {x : Call (PhysicalHost f ell)} {p : Path sel r x} {used : ℕ}
      (previous : ObservedBankPath M retire initial p used) (w : (P).Slot x)
      (actual : PaidBankVisit M retire initial p w) :
      ObservedBankPath M retire initial (.step p w)
        (used+(residentAddonPayload (sourceBankAt M p w).result).length)

theorem true_cache_aware_entries_realize_the_addon_observation
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial) (p : Path sel r c) :
    ObservedBankPath M retire initial p (addonStackBits M p) := by
  induction p with
  | root => exact .root
  | step p w ih =>
    exact .visit ih w (every_legal_paid_occurrence_uses_its_physical_bank M retire initial legal p w).1

#print axioms exact_scoped_read_uses_the_counted_child_bank
#print axioms every_legal_paid_occurrence_uses_its_physical_bank
#print axioms true_cache_aware_entries_realize_the_addon_observation
end
end J6R53PeakAddon
