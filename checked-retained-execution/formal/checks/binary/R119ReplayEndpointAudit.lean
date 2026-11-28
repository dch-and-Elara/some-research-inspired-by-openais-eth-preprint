import Lean
import CanonicalChosenInstance
import CanonicalFreshPhysicalCount
import CanonicalFreshPhysicalTime
import J6R111FreshStartupBinding
import J6R116FreshPhysicalRetained
import J6R116ReadyFromHeld
import J6R116ReadyFromHeldMeter
import J6R116RetainedExteriorPeakChart
import J6R117HeldPhysicalImage
import J6R117RetainedExteriorClockFinish
import J6R118FinalRawMeasuredClock
import J6R118ReadyRootClockImage
import J6R52FreshShapePaidSetup
import Paper6R119LiteralSourceRun
import Paper6R119PhysicalSpace
import Paper6SourceSize

open Lean Elab Command
set_option warningAsError true
set_option pp.fullNames true

#check Paper6CanonicalChosenInstance.actual_chosen_order_is_the_metered_prefix
#print axioms Paper6CanonicalChosenInstance.actual_chosen_order_is_the_metered_prefix
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6CanonicalChosenInstance.actual_chosen_order_is_the_metered_prefix
    | throwError "Missing imported declaration Paper6CanonicalChosenInstance.actual_chosen_order_is_the_metered_prefix"
  unless env.header.moduleNames[idx.toNat]? == some `CanonicalChosenInstance do
    throwError "Paper6CanonicalChosenInstance.actual_chosen_order_is_the_metered_prefix was not declared by CanonicalChosenInstance"

#check Paper6CanonicalChosenInstance.the_paid_table_matches_every_actual_chosen_prefix
#print axioms Paper6CanonicalChosenInstance.the_paid_table_matches_every_actual_chosen_prefix
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6CanonicalChosenInstance.the_paid_table_matches_every_actual_chosen_prefix
    | throwError "Missing imported declaration Paper6CanonicalChosenInstance.the_paid_table_matches_every_actual_chosen_prefix"
  unless env.header.moduleNames[idx.toNat]? == some `CanonicalChosenInstance do
    throwError "Paper6CanonicalChosenInstance.the_paid_table_matches_every_actual_chosen_prefix was not declared by CanonicalChosenInstance"

#check J6R114PrescribedReceipts.runFreshBinaryOrderCount
#print axioms J6R114PrescribedReceipts.runFreshBinaryOrderCount
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.runFreshBinaryOrderCount
    | throwError "Missing imported declaration J6R114PrescribedReceipts.runFreshBinaryOrderCount"
  unless env.header.moduleNames[idx.toNat]? == some `CanonicalFreshPhysicalCount do
    throwError "J6R114PrescribedReceipts.runFreshBinaryOrderCount was not declared by CanonicalFreshPhysicalCount"

#check J6R114PrescribedReceipts.binary_order_actual_run_counts_the_original_CNF
#print axioms J6R114PrescribedReceipts.binary_order_actual_run_counts_the_original_CNF
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.binary_order_actual_run_counts_the_original_CNF
    | throwError "Missing imported declaration J6R114PrescribedReceipts.binary_order_actual_run_counts_the_original_CNF"
  unless env.header.moduleNames[idx.toNat]? == some `CanonicalFreshPhysicalCount do
    throwError "J6R114PrescribedReceipts.binary_order_actual_run_counts_the_original_CNF was not declared by CanonicalFreshPhysicalCount"

#check J6R114PrescribedReceipts.freshBinaryExactRows
#print axioms J6R114PrescribedReceipts.freshBinaryExactRows
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.freshBinaryExactRows
    | throwError "Missing imported declaration J6R114PrescribedReceipts.freshBinaryExactRows"
  unless env.header.moduleNames[idx.toNat]? == some `CanonicalFreshPhysicalCount do
    throwError "J6R114PrescribedReceipts.freshBinaryExactRows was not declared by CanonicalFreshPhysicalCount"

#check J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts
#print axioms J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts
    | throwError "Missing imported declaration J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts"
  unless env.header.moduleNames[idx.toNat]? == some `CanonicalFreshPhysicalCount do
    throwError "J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts was not declared by CanonicalFreshPhysicalCount"

#check J6R114PrescribedReceipts.binary_order_ready_fresh_count_and_time
#print axioms J6R114PrescribedReceipts.binary_order_ready_fresh_count_and_time
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.binary_order_ready_fresh_count_and_time
    | throwError "Missing imported declaration J6R114PrescribedReceipts.binary_order_ready_fresh_count_and_time"
  unless env.header.moduleNames[idx.toNat]? == some `CanonicalFreshPhysicalTime do
    throwError "J6R114PrescribedReceipts.binary_order_ready_fresh_count_and_time was not declared by CanonicalFreshPhysicalTime"

#check J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts_and_time
#print axioms J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts_and_time
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts_and_time
    | throwError "Missing imported declaration J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts_and_time"
  unless env.header.moduleNames[idx.toNat]? == some `CanonicalFreshPhysicalTime do
    throwError "J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts_and_time was not declared by CanonicalFreshPhysicalTime"

#check J6R111FreshStartupBinding.literal_chosen_startup_uses_original_closed_input_rate
#print axioms J6R111FreshStartupBinding.literal_chosen_startup_uses_original_closed_input_rate
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R111FreshStartupBinding.literal_chosen_startup_uses_original_closed_input_rate
    | throwError "Missing imported declaration J6R111FreshStartupBinding.literal_chosen_startup_uses_original_closed_input_rate"
  unless env.header.moduleNames[idx.toNat]? == some `J6R111FreshStartupBinding do
    throwError "J6R111FreshStartupBinding.literal_chosen_startup_uses_original_closed_input_rate was not declared by J6R111FreshStartupBinding"

#check J6R114PrescribedReceipts.fresh_physical_execution_counts_the_original_CNF_and_pays_actual_startup
#print axioms J6R114PrescribedReceipts.fresh_physical_execution_counts_the_original_CNF_and_pays_actual_startup
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.fresh_physical_execution_counts_the_original_CNF_and_pays_actual_startup
    | throwError "Missing imported declaration J6R114PrescribedReceipts.fresh_physical_execution_counts_the_original_CNF_and_pays_actual_startup"
  unless env.header.moduleNames[idx.toNat]? == some `J6R116FreshPhysicalRetained do
    throwError "J6R114PrescribedReceipts.fresh_physical_execution_counts_the_original_CNF_and_pays_actual_startup was not declared by J6R116FreshPhysicalRetained"

#check J6R114PrescribedReceipts.freshPhysicalPlanFromHeldSource
#print axioms J6R114PrescribedReceipts.freshPhysicalPlanFromHeldSource
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.freshPhysicalPlanFromHeldSource
    | throwError "Missing imported declaration J6R114PrescribedReceipts.freshPhysicalPlanFromHeldSource"
  unless env.header.moduleNames[idx.toNat]? == some `J6R116FreshPhysicalRetained do
    throwError "J6R114PrescribedReceipts.freshPhysicalPlanFromHeldSource was not declared by J6R116FreshPhysicalRetained"

#check J6R114PrescribedReceipts.fresh_posted_and_mounted_payload_has_literal_source_scale
#print axioms J6R114PrescribedReceipts.fresh_posted_and_mounted_payload_has_literal_source_scale
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.fresh_posted_and_mounted_payload_has_literal_source_scale
    | throwError "Missing imported declaration J6R114PrescribedReceipts.fresh_posted_and_mounted_payload_has_literal_source_scale"
  unless env.header.moduleNames[idx.toNat]? == some `J6R116FreshPhysicalRetained do
    throwError "J6R114PrescribedReceipts.fresh_posted_and_mounted_payload_has_literal_source_scale was not declared by J6R116FreshPhysicalRetained"

#check J6R116ReadyFromHeld.actual_held_retained_payload_has_source_scale
#print axioms J6R116ReadyFromHeld.actual_held_retained_payload_has_source_scale
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R116ReadyFromHeld.actual_held_retained_payload_has_source_scale
    | throwError "Missing imported declaration J6R116ReadyFromHeld.actual_held_retained_payload_has_source_scale"
  unless env.header.moduleNames[idx.toNat]? == some `J6R116ReadyFromHeld do
    throwError "J6R116ReadyFromHeld.actual_held_retained_payload_has_source_scale was not declared by J6R116ReadyFromHeld"

#check J6R116ReadyFromHeld.the_actual_preparer_returns_source_scale
#print axioms J6R116ReadyFromHeld.the_actual_preparer_returns_source_scale
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R116ReadyFromHeld.the_actual_preparer_returns_source_scale
    | throwError "Missing imported declaration J6R116ReadyFromHeld.the_actual_preparer_returns_source_scale"
  unless env.header.moduleNames[idx.toNat]? == some `J6R116ReadyFromHeldMeter do
    throwError "J6R116ReadyFromHeld.the_actual_preparer_returns_source_scale was not declared by J6R116ReadyFromHeldMeter"

#check J6R116RetainedExteriorPeak.actual_paid_chart_and_retained_exterior_path_take_one_named_maximum
#print axioms J6R116RetainedExteriorPeak.actual_paid_chart_and_retained_exterior_path_take_one_named_maximum
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R116RetainedExteriorPeak.actual_paid_chart_and_retained_exterior_path_take_one_named_maximum
    | throwError "Missing imported declaration J6R116RetainedExteriorPeak.actual_paid_chart_and_retained_exterior_path_take_one_named_maximum"
  unless env.header.moduleNames[idx.toNat]? == some `J6R116RetainedExteriorPeakChart do
    throwError "J6R116RetainedExteriorPeak.actual_paid_chart_and_retained_exterior_path_take_one_named_maximum was not declared by J6R116RetainedExteriorPeakChart"

#check J6R117HeldPhysicalImage.useTheActualHeldConfiguration
#print axioms J6R117HeldPhysicalImage.useTheActualHeldConfiguration
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R117HeldPhysicalImage.useTheActualHeldConfiguration
    | throwError "Missing imported declaration J6R117HeldPhysicalImage.useTheActualHeldConfiguration"
  unless env.header.moduleNames[idx.toNat]? == some `J6R117HeldPhysicalImage do
    throwError "J6R117HeldPhysicalImage.useTheActualHeldConfiguration was not declared by J6R117HeldPhysicalImage"

#check J6R117RetainedExteriorClock.actual_prescribed_exterior_clock_with_real_first_and_retained_subtrees
#print axioms J6R117RetainedExteriorClock.actual_prescribed_exterior_clock_with_real_first_and_retained_subtrees
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R117RetainedExteriorClock.actual_prescribed_exterior_clock_with_real_first_and_retained_subtrees
    | throwError "Missing imported declaration J6R117RetainedExteriorClock.actual_prescribed_exterior_clock_with_real_first_and_retained_subtrees"
  unless env.header.moduleNames[idx.toNat]? == some `J6R117RetainedExteriorClockFinish do
    throwError "J6R117RetainedExteriorClock.actual_prescribed_exterior_clock_with_real_first_and_retained_subtrees was not declared by J6R117RetainedExteriorClockFinish"

#check J6R114PrescribedReceipts.original_ready_fresh_run_counts_and_pays_the_source_clock
#print axioms J6R114PrescribedReceipts.original_ready_fresh_run_counts_and_pays_the_source_clock
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.original_ready_fresh_run_counts_and_pays_the_source_clock
    | throwError "Missing imported declaration J6R114PrescribedReceipts.original_ready_fresh_run_counts_and_pays_the_source_clock"
  unless env.header.moduleNames[idx.toNat]? == some `J6R118FinalRawMeasuredClock do
    throwError "J6R114PrescribedReceipts.original_ready_fresh_run_counts_and_pays_the_source_clock was not declared by J6R118FinalRawMeasuredClock"

#check J6R118ReadyRootClock.actual_posted_ready_root_has_its_source_seed
#print axioms J6R118ReadyRootClock.actual_posted_ready_root_has_its_source_seed
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R118ReadyRootClock.actual_posted_ready_root_has_its_source_seed
    | throwError "Missing imported declaration J6R118ReadyRootClock.actual_posted_ready_root_has_its_source_seed"
  unless env.header.moduleNames[idx.toNat]? == some `J6R118ReadyRootClockImage do
    throwError "J6R118ReadyRootClock.actual_posted_ready_root_has_its_source_seed was not declared by J6R118ReadyRootClockImage"

#check J6R52FreshShape.generated_fresh_root_uses_literal_source_cutoff
#print axioms J6R52FreshShape.generated_fresh_root_uses_literal_source_cutoff
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R52FreshShape.generated_fresh_root_uses_literal_source_cutoff
    | throwError "Missing imported declaration J6R52FreshShape.generated_fresh_root_uses_literal_source_cutoff"
  unless env.header.moduleNames[idx.toNat]? == some `J6R52FreshShapePaidSetup do
    throwError "J6R52FreshShape.generated_fresh_root_uses_literal_source_cutoff was not declared by J6R52FreshShapePaidSetup"

#check J6R52FreshShape.generated_fresh_odd_precision
#print axioms J6R52FreshShape.generated_fresh_odd_precision
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R52FreshShape.generated_fresh_odd_precision
    | throwError "Missing imported declaration J6R52FreshShape.generated_fresh_odd_precision"
  unless env.header.moduleNames[idx.toNat]? == some `J6R52FreshShapePaidSetup do
    throwError "J6R52FreshShape.generated_fresh_odd_precision was not declared by J6R52FreshShapePaidSetup"

#check J6R114PrescribedReceipts.runAtLiteralSourcePrecision
#print axioms J6R114PrescribedReceipts.runAtLiteralSourcePrecision
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.runAtLiteralSourcePrecision
    | throwError "Missing imported declaration J6R114PrescribedReceipts.runAtLiteralSourcePrecision"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6R119LiteralSourceRun do
    throwError "J6R114PrescribedReceipts.runAtLiteralSourcePrecision was not declared by Paper6R119LiteralSourceRun"

#check J6R114PrescribedReceipts.literal_source_startup_emits_the_padded_source_ordinal
#print axioms J6R114PrescribedReceipts.literal_source_startup_emits_the_padded_source_ordinal
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.literal_source_startup_emits_the_padded_source_ordinal
    | throwError "Missing imported declaration J6R114PrescribedReceipts.literal_source_startup_emits_the_padded_source_ordinal"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6R119LiteralSourceRun do
    throwError "J6R114PrescribedReceipts.literal_source_startup_emits_the_padded_source_ordinal was not declared by Paper6R119LiteralSourceRun"

#check J6R114PrescribedReceipts.literal_source_run_counts_and_pays_the_same_clock
#print axioms J6R114PrescribedReceipts.literal_source_run_counts_and_pays_the_same_clock
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.literal_source_run_counts_and_pays_the_same_clock
    | throwError "Missing imported declaration J6R114PrescribedReceipts.literal_source_run_counts_and_pays_the_same_clock"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6R119LiteralSourceRun do
    throwError "J6R114PrescribedReceipts.literal_source_run_counts_and_pays_the_same_clock was not declared by Paper6R119LiteralSourceRun"

#check J6R114PrescribedReceipts.posted_row_workspace_uses_source_size
#print axioms J6R114PrescribedReceipts.posted_row_workspace_uses_source_size
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``J6R114PrescribedReceipts.posted_row_workspace_uses_source_size
    | throwError "Missing imported declaration J6R114PrescribedReceipts.posted_row_workspace_uses_source_size"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6R119PhysicalSpace do
    throwError "J6R114PrescribedReceipts.posted_row_workspace_uses_source_size was not declared by Paper6R119PhysicalSpace"

#check Paper6SourceSize.sourceNativeSize
#print axioms Paper6SourceSize.sourceNativeSize
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.sourceNativeSize
    | throwError "Missing imported declaration Paper6SourceSize.sourceNativeSize"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.sourceNativeSize was not declared by Paper6SourceSize"

#check Paper6SourceSize.sourceNativeSize_le_wires
#print axioms Paper6SourceSize.sourceNativeSize_le_wires
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.sourceNativeSize_le_wires
    | throwError "Missing imported declaration Paper6SourceSize.sourceNativeSize_le_wires"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.sourceNativeSize_le_wires was not declared by Paper6SourceSize"

#check Paper6SourceSize.sourcePaddedSize
#print axioms Paper6SourceSize.sourcePaddedSize
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.sourcePaddedSize
    | throwError "Missing imported declaration Paper6SourceSize.sourcePaddedSize"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.sourcePaddedSize was not declared by Paper6SourceSize"

#check Paper6SourceSize.padded_size_eq
#print axioms Paper6SourceSize.padded_size_eq
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.padded_size_eq
    | throwError "Missing imported declaration Paper6SourceSize.padded_size_eq"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.padded_size_eq was not declared by Paper6SourceSize"

#check Paper6SourceSize.sourceInitialPrecision
#print axioms Paper6SourceSize.sourceInitialPrecision
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.sourceInitialPrecision
    | throwError "Missing imported declaration Paper6SourceSize.sourceInitialPrecision"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.sourceInitialPrecision was not declared by Paper6SourceSize"

#check Paper6SourceSize.sourceInitialPrecision_eq
#print axioms Paper6SourceSize.sourceInitialPrecision_eq
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.sourceInitialPrecision_eq
    | throwError "Missing imported declaration Paper6SourceSize.sourceInitialPrecision_eq"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.sourceInitialPrecision_eq was not declared by Paper6SourceSize"

#check Paper6SourceSize.sourceInitialPrecision_pos
#print axioms Paper6SourceSize.sourceInitialPrecision_pos
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.sourceInitialPrecision_pos
    | throwError "Missing imported declaration Paper6SourceSize.sourceInitialPrecision_pos"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.sourceInitialPrecision_pos was not declared by Paper6SourceSize"

#check Paper6SourceSize.sourceInitialPrecision_le_sq
#print axioms Paper6SourceSize.sourceInitialPrecision_le_sq
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.sourceInitialPrecision_le_sq
    | throwError "Missing imported declaration Paper6SourceSize.sourceInitialPrecision_le_sq"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.sourceInitialPrecision_le_sq was not declared by Paper6SourceSize"

#check Paper6SourceSize.sourcePaddedSize_ceiling
#print axioms Paper6SourceSize.sourcePaddedSize_ceiling
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.sourcePaddedSize_ceiling
    | throwError "Missing imported declaration Paper6SourceSize.sourcePaddedSize_ceiling"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.sourcePaddedSize_ceiling was not declared by Paper6SourceSize"

#check Paper6SourceSize.subdivision_clog_eq
#print axioms Paper6SourceSize.subdivision_clog_eq
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? ``Paper6SourceSize.subdivision_clog_eq
    | throwError "Missing imported declaration Paper6SourceSize.subdivision_clog_eq"
  unless env.header.moduleNames[idx.toNat]? == some `Paper6SourceSize do
    throwError "Paper6SourceSize.subdivision_clog_eq was not declared by Paper6SourceSize"

open Lean Elab Command

private def meterArg (e : Expr) (meterType : Name) (field : Name) (projection : Nat) :
    Option Expr :=
  match e with
  | .proj structureName index arg =>
      if structureName == meterType && index == projection then some arg else none
  | _ => if e.getAppFn.isConstOf field then e.getAppArgs.back? else none

private partial def stripBinders (e : Expr) : Expr :=
  match e with
  | .forallE _ _ body _ | .letE _ _ _ body _ => stripBinders body
  | .mdata _ body => stripBinders body
  | _ => e

private partial def namedMeterConjunction (meter : Name) (e : Expr) (depth : Option Nat := none) :
    Option (Nat × Expr × Expr) :=
  match e with
  | .forallE _ _ body _ => namedMeterConjunction meter body (depth.map (· + 1))
  | .letE _ _ value body _ =>
      if value.getAppFn.isConstOf meter then
        if depth.isSome then none else namedMeterConjunction meter body (some 0)
      else
        namedMeterConjunction meter body (depth.map (· + 1))
  | .mdata _ body => namedMeterConjunction meter body depth
  | _ =>
      if e.getAppFn.isConstOf `And then do
        let k ← depth
        let #[left, right] := e.getAppArgs | none
        pure (k, left, right)
      else none

/-- Audit the public declaration types structurally, without reducing the
meter or searching for separately exhibited executions. -/
def auditNamedMeter (count clock meter meterType resultField stepField : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some countDecl := env.find? count | throwError "count endpoint absent"
  let some clockDecl := env.find? clock | throwError "clock endpoint absent"
  let countType := stripBinders countDecl.type
  let #[_, countLhs, _] := countType.getAppArgs | throwError "count endpoint is not an equality"
  let countProjection := countLhs.find? fun e =>
    ((meterArg e meterType resultField 0).map fun x => x.getAppFn.isConstOf meter).getD false
  unless countType.getAppFn.isConstOf `Eq && countProjection.isSome do
    throwError "count endpoint does not state equality on the named meter result"
  let some (k, left, right) := namedMeterConjunction meter clockDecl.type
    | throwError "clock endpoint has no unique named let-bound meter in its conjunction"
  let isSame (field : Name) (index : Nat) (e : Expr) : Bool :=
    meterArg e meterType field index == some (.bvar k)
  let #[_, answer, _] := left.getAppArgs | throwError "count conjunct is not an equality"
  let #[_, _, steps, _] := right.getAppArgs | throwError "clock conjunct is not an inequality"
  unless left.getAppFn.isConstOf `Eq &&
      (answer.find? (isSame resultField 0)).isSome &&
      right.getAppFn.isConstOf `LE.le && isSame stepField 1 steps do
    throwError "count and clock do not project result and steps of the same named let-bound meter"
  logInfo "R119 same-run audit passed"

run_cmd auditNamedMeter `J6R114PrescribedReceipts.binary_order_actual_run_counts_the_original_CNF `J6R114PrescribedReceipts.binary_order_ready_fresh_count_and_time `J6R114PrescribedReceipts.runFreshBinaryOrderCount `AOracleMachineTime.Meter `AOracleMachineTime.Meter.result `AOracleMachineTime.Meter.steps

run_cmd auditNamedMeter `J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts `J6R114PrescribedReceipts.binary_order_at_literal_source_precision_counts_and_time `J6R114PrescribedReceipts.runFreshBinaryOrderCount `AOracleMachineTime.Meter `AOracleMachineTime.Meter.result `AOracleMachineTime.Meter.steps
