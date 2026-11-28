import J6R54PeakInputCore
import J6R54PeakInputInstall

/-! This is the actual paid installation over the StoredSite field
itself, not installation of an unrelated coherent list. At its
named row boundary the complete raw input and selected already
copied indexed rows are bounded together. -/
namespace J6R54PeakInput
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6R34ChildPath J6R36ChildFramedRoute J6R41StructuredAllPaths
open J1PPrinted J6ActiveRun J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R50SourceProducer J6R51Peak J6R51ParentFrames
open J6R52CacheWhole J6R53PeakAddon

set_option autoImplicit false
set_option maxRecDepth 3750
set_option maxHeartbeats 18500000
set_option maxSynthPendingDepth 12
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}

theorem native_install_prefix_and_the_stored_raw_field
    (X : StoredSite T v key prec tw bw page) (before after : List (Port v.parent.host.Edge))
    (split : X.birth.native.physical.order=before++after) :
    let S := X.site
    let physical := X.birth.native.physical
    let heads := before.map (fun x=>paidIndexHead (physical.record x) (S.aux x))
    let suffix := installAddons (after.map physical.record) (after.map S.aux)
    let paid := installResidentBank X
    let selected := (paid.result.rows.take before.length).flatMap indexedAddonBits
    S.install=resumePaidIndexHeads heads suffix ∧
      paid.steps=(resumePaidIndexHeads heads suffix).steps ∧
      paid.result.rows.take before.length=heads.map Meter.result ∧
      (storedRawBits X).length+selected.length≤
        (2*v.parent.edges)*addonCap S.ownerWidth (dim v) key prec page+
          before.length*(X.birth.port+addonCap S.ownerWidth (dim v) key prec page) := by
  let S := X.site
  let physical := X.birth.native.physical
  let paid := installResidentBank X
  have rawExact : S.input=(before++after).map S.aux := S.aligned.trans (congrArg (List.map S.aux) split)
  have orderExact : physical.raw=(before++after).map physical.record :=
    physical.source.trans (congrArg (List.map physical.record) split)
  have same : S.install=installAddons ((before++after).map physical.record) ((before++after).map S.aux) := by
    change installAddons physical.raw S.input=_
    rw [rawExact,orderExact]
  have paused : S.install=resumePaidIndexHeads
      (before.map (fun x=>paidIndexHead (physical.record x) (S.aux x)))
      (installAddons (after.map physical.record) (after.map S.aux)) := by
    rw [same,List.map_append,List.map_append]
    exact actual_index_installer_resumes_after_paid_heads physical.record S.aux before _ _
  have snapshot : paid.result.rows.take before.length=
      before.map (fun x=>(paidIndexHead (physical.record x) (S.aux x)).result) := by
    rw [(resident_install_exact X).1,same]
    exact selected_index_heads_are_the_actual_installed_rows physical.record S.aux before after
  have bound : ((paid.result.rows.take before.length).flatMap indexedAddonBits).length≤
      before.length*(X.birth.port+addonCap S.ownerWidth (dim v) key prec page) := by
    rw [(resident_install_exact X).1,same]
    exact selected_install_prefix_fits_actual_column_width physical.record S.aux before after
  refine ⟨paused,?_ ,?_,?_⟩
  · rw [(resident_install_exact X).2,paused]
  · simpa only [List.map_map,Function.comp_def] using snapshot
  · exact Nat.add_le_add (stored_raw_is_bounded_and_counts_true_parent_halves X).2.2 bound

#print axioms native_install_prefix_and_the_stored_raw_field
end
end J6R54PeakInput
