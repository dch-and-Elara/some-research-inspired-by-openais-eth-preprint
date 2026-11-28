import J6R53PeakAddonVisits
import J6R51OnlineFeeDefs
import J6R49CostActive

/-! Names for the exact local charges of the already checked cached
interpreter. The displayed fees are read from that actual execution;
there is no opaque phase cap or supplied fee schedule. -/
namespace J6R55CachedLedger
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3850
set_option maxHeartbeats 22000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Pg" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)
local notation "Plan₀" => (@Plan f ell s sel)

def cachedTotal (M : OnlineMachine T key prec tw bw page q) (retire : Job→ℕ)
    (initial : Pg) (z : Sigma (Path sel r)) : ℕ :=
  (cacheVisitAt M retire initial z.2).steps

def cacheMountFee (M : OnlineMachine T key prec tw bw page q) :
    {c : Call (PhysicalHost f ell)} → Path sel r c → ℕ
  | _, .root => 0
  | _, .step p w => (sourceMounted (M:=M) p w).steps

def cachedScopeOwn (M : OnlineMachine T key prec tw bw page q) (retire : Job→ℕ) (initial : Pg)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan₀).Slot c) : ℕ :=
  let j := (borns M p w).job
  installedAddonDebit M p w +
    (publishFee (stackBank (borns M) initial p) j.entry j.offset j.built + retire j + 4)

def cachedOwn (M : OnlineMachine T key prec tw bw page q) (retire : Job→ℕ)
    (initial : Pg) (z : Sigma (Path sel r)) : ℕ :=
  if stop : z.1.edges≤(SP).cutoff then
    (readLeaf M initial z.2 stop).steps
  else
    let A := preparedActive M z.2 (Nat.lt_of_not_ge stop)
    letI : Fintype ((Plan₀).Slot z.1) := (Plan₀).finiteSlot z.1
    cacheMountFee M z.2+A.steps+streamActiveTariff A.result (reachable_positive T z.2.reached) T.vPositive+
      ∑ w : (Plan₀).Slot z.1,cachedScopeOwn M retire initial z.2 w

theorem cached_leaf_total (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (stop : c.edges≤(SP).cutoff) :
    cachedTotal M retire initial ⟨c,p⟩=(readLeaf M initial p stop).steps := by
  cases p with
  | root =>
    change (runCachedRoot M retire initial).steps=(M.leafRoot stop initial).steps
    rw [runCachedRoot,dif_pos stop]
  | step prev u =>
    let bank := stackBank (borns M) initial (.step prev u)
    let X := sourceState M prev u
    change (runCachedAfter M retire _ prev u X (sourceBankAt M prev u).result bank).steps=
      (M.leafAfter prev u X stop bank).steps
    rw [runCachedAfter,dif_pos stop]

theorem cached_active_total_eq (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (a : (SP).cutoff<c.edges) :
    let A := preparedActive M p a
    cachedTotal M retire initial ⟨c,p⟩=cacheMountFee M p+A.steps+
      (A.result.eval M.modeWidth (reachable_positive T p.reached) T.vPositive hf
        (cachedReadAt M retire initial p a)).steps := by
  cases p with
  | root =>
    simpa only [cachedTotal,cacheVisitAt,cacheMountFee,preparedActive,cachedReadAt,Nat.zero_add] using
      congrArg Meter.steps (actual_root_active_uses_the_exterior_child_reader M retire initial a)
  | step prev u =>
    simpa only [cachedTotal,cacheVisitAt,cacheMountFee,sourceBankAt,preparedActive,cachedReadAt] using
      congrArg Meter.steps (cached_active_phase_uses_the_selected_frame_cache M retire initial prev u a)

theorem cached_read_steps_sum (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (a : (SP).cutoff<c.edges) (legal : ReadyOnStack (borns M) initial)
    (t : Center SP c) (z : Probe SP c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    (cachedReadAt M retire initial p a t z β g).steps =
      cachedScopeOwn M retire initial p w+
        cachedTotal M retire initial ⟨(Plan₀).child c w,.step p w⟩ := by
  have same := congrArg Meter.steps
    (exact_scoped_read_uses_the_counted_child_bank M retire initial legal p a t z β g)
  dsimp only at same ⊢
  rw [same]
  unfold cachedScopeOwn cachedTotal
  dsimp only
  ac_rfl

#print axioms cachedTotal
#print axioms cacheMountFee
#print axioms cachedScopeOwn
#print axioms cachedOwn
#print axioms cached_leaf_total
#print axioms cached_active_total_eq
#print axioms cached_read_steps_sum
end
end J6R55CachedLedger
