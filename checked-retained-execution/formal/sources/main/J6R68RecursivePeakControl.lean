import J6R68RecursivePeakFields
import J6R66ActiveLedger
import J6R51PeakOnlineDirectory
import J6R50PeakStartPrecision

/-! A small, separate projection of current read/control words from
the actual R66 predecessor. The incoming width is dependent, but the
read words and the layout result have independent types. The rest of
the supplier closure is not counted as a header word. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole J6R50Peak
open J6R53PeakAddon J6R54PeakInput J6R63Active J6R64Active J6R66Active J6R62ActivePrep
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 3900
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 6500000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)

def liveCallWords
    (M : OnlineMachine T key prec tw bw page q) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → Σ e : ℕ,Meter (CallWords x prec e)
  | _,.root => ⟨ew,E.inherit B own⟩
  | _,.step p w =>
    let X := sourceState M p w
    let bank := stackBank (borns M) B (.step p w)
    ⟨X.birth.edge,readIncoming X bank rfl⟩

def liveLayoutWord
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) →
      Meter (AtLayout sel (readyAtPath T p a) cw)
  | _,.root,a => E.layout B own a
  | _,.step p w,a => F.layout p w (sourceState M p w) a

variable (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
variable (E : RootInputs T key prec tw bw page cw ew)
variable (B : PageBank f ell key prec tw bw page) (own : OwnsHeader E.header B)

def literalControlBits (p : Path sel r c) (a : (S).cutoff<c.edges) : ℕ :=
  retainedHeaderControlBits (liveCallWords M E B own p).2 (liveLayoutWord M F E B own p a) q

theorem literal_control_bits_exact (p : Path sel r c) (a : (S).cutoff<c.edges) :
    literalControlBits M F E B own p a=prec+(liveCallWords M E B own p).1+q :=
  actual_shared_control_bits_fit_the_fixed_registers (q:=q)
    (liveCallWords M E B own p).2 (liveLayoutWord M F E B own p a)

theorem live_actual_edge_width (fixed addr : ℕ)
    (sizes : EntryWidths (shadow M F E B own) fixed addr) (p : Path sel r c) :
    (liveCallWords M E B own p).1≤max ew fixed := by
  cases p with
  | root => exact Nat.le_max_left _ _
  | step p w =>
    have fit := (sizes p w).1
    have eq : borns (shadow M F E B own) p w=borns M p w :=
      congrArg (fun X : StoredSite T (p.ticket w) key prec tw bw page=>X.birth)
        (shadow_stored_sites_unchanged M F E B own p w)
    rw [eq] at fit
    change (sourceState M p w).birth.edge≤max ew fixed
    have all : (sourceState M p w).birth.edge≤fixedWords (borns M p w) := by
      unfold fixedWords borns
      exact Nat.le_add_left _ _
    exact all.trans (fit.trans (Nat.le_max_right _ _))

def literalControlPath :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _,.root => 0
  | _,.step p w => literalControlPath p+literalControlBits M F E B own p w.property

theorem literal_control_path_has_absolute_cap
    (fixed addr : ℕ) (sizes : EntryWidths (shadow M F E B own) fixed addr) (p : Path sel r c) :
    literalControlPath M F E B own p≤pathLimit s C*(prec+max ew fixed+q) := by
  let width := prec+max ew fixed+q
  have one : literalControlPath M F E B own p≤moves p*width := by
    induction p with
    | root => exact Nat.zero_le _
    | step p w ih =>
      have cur : literalControlBits M F E B own p w.property≤width := by
        rw [literal_control_bits_exact]
        exact Nat.add_le_add_right (Nat.add_le_add_left (live_actual_edge_width M F E B own fixed addr sizes p) _) _
      simpa only [literalControlPath,moves,Nat.add_mul,Nat.one_mul] using Nat.add_le_add ih cur
  exact one.trans (Nat.mul_le_mul_right width (actual_ancestry_moves_any_start cfg sel T.rootStable p))

#print axioms literal_control_bits_exact
#print axioms live_actual_edge_width
#print axioms literal_control_path_has_absolute_cap
end
end J6R68.RecursivePeak