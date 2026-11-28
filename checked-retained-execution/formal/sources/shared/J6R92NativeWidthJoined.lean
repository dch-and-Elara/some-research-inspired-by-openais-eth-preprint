import J6R92NativeWidthFirst
import J6R66LeafTariffExterior

/-! One newly configured R55/R51 machine, not an equivalence of
existing encoded runs. At new creation, both callbacks use the least
width of the real raw roster. Original consumed ancestor contexts
stay as they were published. -/
namespace J6R92NativeWidth
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R54PublicFamily J6R57ScopeFee J6R88ScopeCode
open J6R55BootBodies J6R55TerminalOrigin J6R48GeneratedAddons
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R55TerminalBootJoined J6R53OldOwnerRoot J6R54TerminalBoot J6R54ExteriorOwner
open J6R85ScopeProducer J6R66LeafTariff

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5200
set_option maxHeartbeats 33000000
set_option maxSynthPendingDepth 12

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
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable {own rate : ℕ} {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)
variable (M : (OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate))
variable (A : FirstBodyProgram X gate pad T)
variable (D : OwnerWordsAtBodies X gate pad root A)
variable (B : (PageBank f ell key prec tw bw (pageKeyWidth m+pad)))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)

def withMinimalNativeCode : OnlineMachine T key prec tw bw Pg rate :=
  withJoinedBoot X gate pad root (withMinimalDemand M) (minimalFirstProgram X gate pad A)
    (minimalFirstOwners X gate pad A root D) B live rootInj

local notation "M1" => (withMinimalNativeCode X gate pad root M A D B live rootInj)

theorem selected_first_factory_is_still_the_original_body_and_owner_mount :
    ExactPrintedBoot X M1 gate :=
  actual_joined_boot_is_literal X gate pad root (withMinimalDemand M)
    (minimalFirstProgram X gate pad A) (minimalFirstOwners X gate pad A root D) B live rootInj

theorem same_new_runtime_selects_width_for_every_actual_created_packet
    {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (w : (Plan sel).Slot c) :
    let I := (sourceState M1 p w).input
    I.code=leastRosterCode I.geometry.modes.length := by
  cases p with
  | root =>
    have src := joined_source_identity X gate pad root (withMinimalDemand M)
      (minimalFirstProgram X gate pad A) (minimalFirstOwners X gate pad A root D) B live rootInj w
    change ((M1).initial w).result.input= _ at src
    change ((M1).initial w).result.input.code=
      leastRosterCode ((M1).initial w).result.input.geometry.modes.length
    rw [src]
    exact (literal_first_body_uses_the_new_width_and_same_physical_writer X gate pad A w).1
  | step prev u =>
    let state := sourceState M1 prev u
    let load := M.demand state w
    exact (selected_local_load_keeps_exact_directory_and_roster load.result).2.2.2.2.2.2

theorem same_new_runtime_fits_actual_native_label_bound
    {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (w : (Plan sel).Slot c) :
    (sourceState M1 p w).input.code≤canonicalSourceCode s C (Ext).prec := by
  let I := (sourceState M1 p w).input
  have eq := same_new_runtime_selects_width_for_every_actual_created_packet X gate pad root M A D B live rootInj p w
  change I.code=leastRosterCode I.geometry.modes.length at eq
  change I.code≤_
  rw [eq]
  exact (exact_native_roster_code_lower_and_choice p w I).2.1

theorem same_new_runtime_atlas_without_supplied_code_cap
    (physicalSizeEq : s=physicalSize m native) (hn : native≤m) (baseFit : base≤C*s)
    {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (w : (Plan sel).Slot c) :
    AtlasFootprint (sourceState M1 p w).input
      (atlasSourceRoof s C (Ext).prec ell Pg tw bw (6*Nat.clog 2 s)) := by
  have receiver : (Ext).prec≤161*C*s^2 := by
    rw [physicalSizeEq] at baseFit ⊢
    exact literal_exterior_start_precision_quadratic X hn cfg.constPos baseFit
  exact true_atlas_from_bounded_native_code_choice M1 p w receiver
    (same_new_runtime_fits_actual_native_label_bound X gate pad root M A D B live rootInj p w)

#print axioms withMinimalNativeCode
#print axioms selected_first_factory_is_still_the_original_body_and_owner_mount
#print axioms same_new_runtime_selects_width_for_every_actual_created_packet
#print axioms same_new_runtime_fits_actual_native_label_bound
#print axioms same_new_runtime_atlas_without_supplied_code_cap
end
end J6R92NativeWidth
