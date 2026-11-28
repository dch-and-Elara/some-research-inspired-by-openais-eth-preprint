import J6R68RecursivePeakBound
import J6R68RecursivePeakRosters
import J6R68RecursivePeakNativeRoof
import J6R68RecursivePeakVisit

/-! The real R66 path, including a suspended parent during child I/O
and one current active-centre output. Nothing in this reserve claims
a bound on arbitrary supplier scratch or the entire machine heap. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R50Peak J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole
open J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R66.BootPeak
open J6R63Active J6R64Active J6R66Active J6R49DFS J6ActiveSchedule
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4500
set_option maxHeartbeats 18000000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

variable (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
variable (E : RootInputs T key prec tw bw page cw ew)
variable (B : PageBank f ell key prec tw bw page) (own : OwnsHeader E.header B) (retire : PageJob f ell key prec tw bw page→ℕ)

/-- A single same-execution reserve; the active-centre allowance
counts only the present returned raw record/tape views, not the
array-generating handler. -/
theorem real_r66_child_publication_and_native_tape_selected_peak
    (shared : ℕ)
    (fits : q≤uniformWidth s C) (pageBound high fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit (shadow M F E B own) pageBound)
    (hi : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges),
      x.prec+(liveActiveAt M F E B own p a).result.extraPrecision≤high)
    (sizes : EntryWidths (shadow M F E B own) fixed addr)
    (boot : BootBodyWidth (shadow M F E B own) seed)
    (owners : OwnerWidth (shadow M F E B own) owner)
    (legal : ReadyOnStack (borns M) B) (p : Path sel r c) (w : (P).Slot c) :
    let K := max ew fixed
    let next := Path.step p w
    let Q := shadow M F E B own
    let roof := recursiveResidentRoof shared B r pageBound high fixed addr seed owner s C+
      pathLimit s C*(prec+K+q)+
      pathLimit s C*suspendedRosterCap s C (absolutePrecision s r.edges r.prec)
    let producer := prec+K+q+nativeCentreRoof s C cw q (absolutePrecision s r.edges r.prec)
    liveReaderAt M F retire B p w.property=cachedReadAt Q retire B p w.property ∧
    activeAt Q p w.property=liveActiveAt M F E B own p w.property ∧
    ∃ b k,ObservedRosterPause Q retire B next b k ∧
      (∀ point,recursiveStagingBits M B p w shared b point+literalControlPath M F E B own next+k≤roof) ∧
      recursiveResidentBits shared M B next b+literalControlPath M F E B own next+k≤roof ∧
      (∀ (active : (S).cutoff<((P).child c w).edges) (t : Center S ((P).child c w)),
        recursiveResidentBits shared M B next b+literalControlPath M F E B own next+k+
          literalControlBits M F E B own next active+liveCentreOutputBits M F E B own next active t≤
        roof+producer) := by
  let K := max ew fixed
  let next := Path.step p w
  obtain ⟨b,obs,entered,staged⟩ := all_recursive_write_points_fit_the_next_actual_resident_bound
    M F E B own retire shared fits pageBound high fixed addr seed owner
    pageFit hi sizes boot owners legal p w
  obtain ⟨k,roster,counted⟩ := same_actual_pauses_retain_the_actual_encoded_rosters obs
  have paused := literal_control_path_has_absolute_cap M F E B own fixed addr sizes next
  refine ⟨every_r66_live_reader_is_the_exact_metered_scoped_callback M F E retire B own p w.property,
    same_actual_preparation_for_pause M F E B own p w.property,
    b,k,roster,fun point=>Nat.add_le_add (Nat.add_le_add (staged point) paused) counted,
    Nat.add_le_add (Nat.add_le_add entered paused) counted,?_⟩
  intro active t
  have cg : literalControlBits M F E B own next active≤prec+K+q := by
    rw [literal_control_bits_exact]
    exact Nat.add_le_add_right
      (Nat.add_le_add_left (live_actual_edge_width M F E B own fixed addr sizes next) _) _
  have tk := actual_raw_centre_outputs_have_uniform_selected_roof M F E B own next active t
  simpa only [Nat.add_assoc] using Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add entered paused) counted) (Nat.add_le_add cg tk)


#print axioms real_r66_child_publication_and_native_tape_selected_peak
end
end J6R68.RecursivePeak