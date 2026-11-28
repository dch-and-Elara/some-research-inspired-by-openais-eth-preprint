import J6R68RecursivePeakRosters
import J6R68RecursivePeakBound
import J6R68RecursivePeakVisit

/-! Charge the suspended roster in addition to the existing true
cursor, words and arithmetic fields. The actual R66 callback and
the observer reader agree at this exact physical slot, not just
after a run has restored its directory. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole J6R50Peak
open J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R66.BootPeak
open J6R63Active J6R64Active J6R66Active J6R49DFS
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4530
set_option maxHeartbeats 16500000
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

theorem actual_recursive_selected_peak_includes_suspended_rosters
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (retire : J→ℕ) (shared : ℕ) (fits : q≤uniformWidth s C)
    (pageBound high fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit (shadow M F E B own) pageBound)
    (hi : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges),
      x.prec+(liveActiveAt M F E B own p a).result.extraPrecision≤high)
    (sizes : EntryWidths (shadow M F E B own) fixed addr)
    (boot : BootBodyWidth (shadow M F E B own) seed)
    (owners : OwnerWidth (shadow M F E B own) owner)
    (legal : ReadyOnStack (borns M) B) (p : Path sel r c) (w : (P).Slot c) :
    let Q := shadow M F E B own
    let next := Path.step p w
    let roof := recursiveResidentRoof shared B r pageBound high fixed addr seed owner s C+
      pathLimit s C*suspendedRosterCap s C (absolutePrecision s r.edges r.prec)
    liveReaderAt M F retire B p w.property=cachedReadAt Q retire B p w.property ∧
    activeAt Q p w.property=liveActiveAt M F E B own p w.property ∧
    ∃ b k,ObservedRosterPause Q retire B next b k ∧
      recursiveResidentBits shared M B next b+k≤roof ∧
      ∀ phase,recursiveStagingBits M B p w shared b phase+k≤roof := by
  obtain ⟨b,seen,entered,staged⟩ := all_recursive_write_points_fit_the_next_actual_resident_bound
    M F E B own retire shared fits pageBound high fixed addr seed owner pageFit hi sizes boot owners legal p w
  obtain ⟨k,roster,cap⟩ := same_actual_pauses_retain_the_actual_encoded_rosters seen
  exact ⟨every_r66_live_reader_is_the_exact_metered_scoped_callback M F E retire B own p w.property,
    same_actual_preparation_for_pause M F E B own p w.property,
    b,k,roster,Nat.add_le_add entered cap,fun phase=>Nat.add_le_add (staged phase) cap⟩

#print axioms actual_recursive_selected_peak_includes_suspended_rosters
end
end J6R68.RecursivePeak