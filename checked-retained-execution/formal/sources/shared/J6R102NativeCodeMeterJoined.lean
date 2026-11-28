import J6R102NativeCodeMeterFirst
import J6R102NativeCodeMeterDemand
import J6R92NativeWidthJoined

/-! The same stock R55 first mount and R51 later demand, with the
literal measured selector run once before each new publication. The
R92 runtime is the comparison on results, not on total time. -/
namespace J6R102NativeCodeMeter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R54PublicFamily J6R57ScopeFee J6R88ScopeCode
open J6R33GeneratedChildSite J6R92NativeWidth J6R17ModeTape J6R14LayoutCost
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5000
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12
open J6R55BootBodies J6R55TerminalOrigin J6R48GeneratedAddons J6R48RawRoute
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R55TerminalBootJoined J6R53OldOwnerRoot J6R54TerminalBoot J6R54ExteriorOwner
open J6R85ScopeProducer J6R66LeafTariff

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Slot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "Pg" => (pageKeyWidth m+pad)
local notation "TicketAt" => (fun w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group) =>
  (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)).ticket w)
variable (A : FirstBodyProgram X gate pad T)
variable {own rate : ℕ} {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (D : OwnerWordsAtBodies X gate pad root A)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)

def firstSlotFor (w : Slot) (L : Meter (OccurrenceInput T (TicketAt w) key prec tw bw Pg))
    (samePage : occurrencePageWord L.result=occurrencePageWord (bodyAtActualSlot X gate pad A w).result) :
    LiteralFirstSlot X gate pad root w T :=
  ⟨L,D.width w,D.name w,D.distinct w,D.keys w,retieBootPorts (D.ports w) samePage⟩

def measuredSlots (w : Slot) : LiteralFirstSlot X gate pad root w T :=
  firstSlotFor X gate pad A root D w
    (bodyAtActualSlot X gate pad (measuredFirstProgram X gate pad A) w)
    ((congrArg occurrencePageWord (measured_first_body_same_and_pays_actual_count X gate pad A w).1).trans
      (literal_first_body_uses_the_new_width_and_same_physical_writer X gate pad A w).2.2.2.1)

def billFirstSlot {w : Slot} (D₀ : LiteralFirstSlot X gate pad root w T) (extra : ℕ) :
    LiteralFirstSlot X gate pad root w T :=
  { D₀ with occurrence := ⟨D₀.occurrence.result,D₀.occurrence.steps+extra⟩ }

theorem firstSlotFor_exact_additive_debit (w : Slot)
    (L K : Meter (OccurrenceInput T (TicketAt w) key prec tw bw Pg)) (extra : ℕ)
    (pageL : occurrencePageWord L.result=occurrencePageWord (bodyAtActualSlot X gate pad A w).result)
    (pageK : occurrencePageWord K.result=occurrencePageWord (bodyAtActualSlot X gate pad A w).result)
    (result : K.result=L.result) (cost : K.steps=L.steps+extra) :
    firstSlotFor X gate pad A root D w K pageK =
      billFirstSlot X gate pad root (firstSlotFor X gate pad A root D w L pageL) extra := by
  have eq : K = ⟨L.result,L.steps+extra⟩ := by
    cases K
    exact congrArg₂ Meter.mk result cost
  subst K
  rfl

theorem selected_first_slot_has_exact_new_bill (w : Slot) :
    let previous := joinedSlots X gate pad root (minimalFirstProgram X gate pad A)
      (minimalFirstOwners X gate pad A root D) w
    measuredSlots X gate pad A root D w = billFirstSlot X gate pad root previous
      (countModes previous.occurrence.result.physical.result.raw.roster.modes).steps := by
  obtain ⟨hr,hc⟩ := measured_first_body_same_and_pays_actual_count X gate pad A w
  have pg := (literal_first_body_uses_the_new_width_and_same_physical_writer X gate pad A w).2.2.2.1
  exact firstSlotFor_exact_additive_debit X gate pad A root D w _ _ _ pg
    ((congrArg occurrencePageWord hr).trans pg) hr hc

theorem physical_initial_adds_only_literal_scan {w : Slot}
    (L : LiteralFirstSlot X gate pad root w T) (extra : ℕ) :
    let old := assembleFirstExterior X gate pad root w L B live rootInj
    let new := assembleFirstExterior X gate pad root w (billFirstSlot X gate pad root L extra) B live rootInj
    new.result=old.result ∧ new.steps=old.steps+extra := by
  refine ⟨rfl,?_⟩
  rw [actual_first_exterior_cost,actual_first_exterior_cost]
  dsimp only [billFirstSlot]
  omega

def withMeteredNativeCode : OnlineMachine T key prec tw bw Pg rate :=
  withGeneratedOrigins X gate pad root (withPaidDemand M) (measuredSlots X gate pad A root D) B live rootInj

local notation "Paid" => (withMeteredNativeCode X gate pad A root M D B live rootInj)
local notation "Prior" => (withMinimalNativeCode X gate pad root M A D B live rootInj)

theorem same_initial_result_and_one_additional_roster_scan (w : Slot) :
    let old := (Prior).initial w
    let new := (Paid).initial w
    new.result=old.result ∧ new.steps=old.steps+
      (countModes old.result.input.physical.result.raw.roster.modes).steps := by
  let prev := joinedSlots X gate pad root (minimalFirstProgram X gate pad A)
    (minimalFirstOwners X gate pad A root D) w
  change let old := assembleFirstExterior X gate pad root w prev B live rootInj
    let new := assembleFirstExterior X gate pad root w (measuredSlots X gate pad A root D w) B live rootInj
    new.result=old.result ∧ new.steps=old.steps+(countModes prev.occurrence.result.physical.result.raw.roster.modes).steps
  rw [selected_first_slot_has_exact_new_bill X gate pad A root D w]
  exact physical_initial_adds_only_literal_scan X gate pad root B live rootInj prev _

theorem same_demand_result_and_one_additional_roster_scan
    {v : Ticket sel Ext} (Q : StoredSite T v key prec tw bw Pg) (w : (Plan sel).Slot v.child) :
    let old := (Prior).demand Q w
    let new := (Paid).demand Q w
    new.result=old.result ∧ new.steps=old.steps+
      (countModes old.result.replay.resident.raw.roster.modes).steps :=
  real_demand_returns_r92_and_bills_the_actual_count_once M Q w

theorem all_selected_stored_sites_are_exactly_r92
    {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (w : (Plan sel).Slot c) :
    sourceState (Paid) p w=sourceState (Prior) p w := by
  induction p with
  | root =>
    exact (same_initial_result_and_one_additional_roster_scan X gate pad A root M D B live rootInj w).1
  | step p u ih =>
    change (((Paid).demand (sourceState (Paid) p u) w).result.advance).next=
      (((Prior).demand (sourceState (Prior) p u) w).result.advance).next
    rw [ih u]
    exact congrArg (fun K=>K.advance.next)
      (same_demand_result_and_one_additional_roster_scan X gate pad A root M D B live rootInj
        (sourceState (Prior) p u) w).1

theorem metered_selected_boot_still_has_the_exact_printed_bodies :
    ExactPrintedBoot X (Paid) gate :=
  origin_seam_retains_only_body_receipt X gate pad root (withPaidDemand M)
    (measuredSlots X gate pad A root D) B live rootInj
    (every_produced_first_slot_has_original_body X gate pad (measuredFirstProgram X gate pad A))

#print axioms firstSlotFor_exact_additive_debit
#print axioms measuredSlots
#print axioms selected_first_slot_has_exact_new_bill
#print axioms physical_initial_adds_only_literal_scan
#print axioms withMeteredNativeCode
#print axioms same_initial_result_and_one_additional_roster_scan
#print axioms same_demand_result_and_one_additional_roster_scan
#print axioms all_selected_stored_sites_are_exactly_r92
#print axioms metered_selected_boot_still_has_the_exact_printed_bodies
end
end J6R102NativeCodeMeter
