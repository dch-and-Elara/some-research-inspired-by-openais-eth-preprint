import J6R102NativeCodeMeterJoined
import J6R57ScopeFeeAtlasGeometry

/-! The additional scan is bounded by the already proved actual
native occurrence footprint, including real row widths. No fee bound
is inferred for a supplied boot/demand circuit from its output shape. -/
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

def nativeCodeScanRoof (U : ℕ) : ℕ := 11+(30*U+21)*U

/-- Standalone version of the two-phase receipt. In the online
interface these two numbers are recorded at different consumers. -/
def runSelectorWord {q : ℕ} (bw : ℕ) (xs : List (RawMode q)) : Meter (Word bw) :=
  (selectCode bw xs).bind PickedCode.write

theorem full_selector_bit_charge {q bw : ℕ} (xs : List (RawMode q)) (positive : 0<bw)
    (fit : leastRosterCode xs.length<2^bw) :
    let v := runSelectorWord bw xs
    v.result=(emitOrdinal bw (leastRosterCode xs.length)).result ∧
      v.steps=(countModes xs).steps+ordinalFee bw (leastRosterCode xs.length) := by
  have h := selected_code_is_old_word xs positive fit
  have hv := congrArg (fun w : Meter (Word bw)=>w.result) h.2.1
  exact ⟨hv,congrArg ((countModes xs).steps+·) h.2.2.1⟩

noncomputable section
section Numeric
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}

theorem actual_roster_scan_from_literal_atlas_footprint
    (I : OccurrenceInput T v key prec tw bw page) (U : ℕ) (foot : AtlasFootprint I U) :
    (countModes I.physical.result.raw.roster.modes).steps≤nativeCodeScanRoof U := by
  let a := (printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth
  have h := actual_raw_roster_scan_is_affine I.geometry
  have dim : a≤U := foot.dim
  have coef : 24*a+6*(I.q+1)+21≤30*U+21 := by have := foot.q; omega
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul coef foot.modeCount) 11)
end Numeric

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
variable (physicalSizeEq : s=physicalSize m native) (hn : native≤m) (baseFit : base≤C*s)

local notation "Paid" => (withMeteredNativeCode X gate pad A root M D B live rootInj)
local notation "Prior" => (withMinimalNativeCode X gate pad root M A D B live rootInj)
local notation "Roof" => (nativeCodeScanRoof (atlasSourceRoof s C (Ext).prec ell Pg tw bw (6*Nat.clog 2 s)))

include physicalSizeEq hn baseFit

theorem same_paid_reached_occurrence_has_printed_code_scan_roof
    {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (w : (Plan sel).Slot c) :
    (countModes (sourceState (Paid) p w).input.physical.result.raw.roster.modes).steps≤Roof := by
  rw [all_selected_stored_sites_are_exactly_r92 X gate pad A root M D B live rootInj p w]
  exact actual_roster_scan_from_literal_atlas_footprint _ _
    (same_new_runtime_atlas_without_supplied_code_cap X gate pad root M A D B live rootInj
      physicalSizeEq hn baseFit p w)

theorem actual_first_callback_has_only_polynomial_extra
    (w : Slot) : ((Paid).initial w).steps≤((Prior).initial w).steps+Roof := by
  rw [(same_initial_result_and_one_additional_roster_scan X gate pad A root M D B live rootInj w).2]
  apply Nat.add_le_add_left
  exact actual_roster_scan_from_literal_atlas_footprint _ _
    (same_new_runtime_atlas_without_supplied_code_cap X gate pad root M A D B live rootInj
      physicalSizeEq hn baseFit (Path.root : Path sel Ext Ext) w)

theorem actual_reached_demand_callback_has_only_polynomial_extra
    {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (u : (Plan sel).Slot c)
    (w : (Plan sel).Slot ((Plan sel).child c u)) :
    let newParent := sourceState (Paid) p u
    let oldParent := sourceState (Prior) p u
    ((Paid).demand newParent w).steps≤((Prior).demand oldParent w).steps+Roof := by
  dsimp only
  rw [all_selected_stored_sites_are_exactly_r92 X gate pad A root M D B live rootInj p u]
  rw [(same_demand_result_and_one_additional_roster_scan X gate pad A root M D B live rootInj
    (sourceState (Prior) p u) w).2]
  apply Nat.add_le_add_left
  exact actual_roster_scan_from_literal_atlas_footprint _ _
    (same_new_runtime_atlas_without_supplied_code_cap X gate pad root M A D B live rootInj
      physicalSizeEq hn baseFit (Path.step p u) w)

#print axioms full_selector_bit_charge
#print axioms actual_roster_scan_from_literal_atlas_footprint
#print axioms same_paid_reached_occurrence_has_printed_code_scan_roof
#print axioms actual_first_callback_has_only_polynomial_extra
#print axioms actual_reached_demand_callback_has_only_polynomial_extra
end
end J6R102NativeCodeMeter
