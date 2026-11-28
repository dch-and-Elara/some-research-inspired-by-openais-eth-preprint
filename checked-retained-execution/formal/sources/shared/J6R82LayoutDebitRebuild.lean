import J6R82LayoutDebitNative
import J6R52CacheWholePrep
import J6R53OldOwnerHeaders
import J6R36RouteConservationGroups

/-! Before the layout callback there is no cache argument. This version
explicitly rebuilds the indexed addon rows and the selected frames from
the same StoredSite, retaining their real fees. It neither moves nor
discounts the later R68 mount for the recursive child reader. -/
namespace J6R82LayoutDebit
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J6R34ChildPath J6R41StructuredAllPaths J6R36ChildFramedRoute
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R48RawRoute J6R34RootAtlas
open J6R49SourceLayout J6R50SourceProducer J6R52CacheWhole J6R51ParentFrames
open J6R68ActiveInputs J6R32ChildResidentTransfer J6R53OldOwner J6R25PreparedSupply
open V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10500000
set_option maxRecDepth 4400
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (X : StoredSite T v key prec tw bw page)
variable (parents : Meter (ParentOwnerHeaders X.site))
variable (fit : v.child.edges<2^q) (oldInj : Function.Injective X.site.oldKey)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
local instance LayoutEdge : Fintype v.child.host.Edge := v.child.host.finiteEdge

def scanMountedIncidence (cached : CachedParentFrames X.site) : Meter (Option (List Incidence)) :=
  let inc := readFramedRows cached.rows
  ⟨inc.result,inc.steps+3⟩

theorem mounted_incidence_is_source_incidence (cached : CachedParentFrames X.site) :
    scanMountedIncidence X cached=sourceIncidence X.site := by
  unfold sourceIncidence
  rw [cached.exactRows]
  rfl

/-- The whole Meter charges the exact header-table acquisition supplied
below, then physical sidecar install, true frame construction and scans. -/
def rebuildNativeIngress :
    Ingress (nativeFull64 X.site parents.result X.canonical fit oldInj) :=
  let addon := installResidentBank X
  let mounted := mountResident X addon.result
  let keys := liveVertexKeys X.site parents.result X.canonical
  let names := writeTargets keys.result.rawRows keys.result.rawCols
  let scan := scanMountedIncidence X mounted.result
  let canonical := nativeIngress X.site parents.result X.canonical fit oldInj
  { paid := ⟨(names.result,scan.result.getD []),
      parents.steps+addon.steps+mounted.steps+(keys.steps+names.steps+scan.steps+5)⟩
    commands := canonical.commands
    incidences := by
      change (scanMountedIncidence X mounted.result).result.getD []=_
      rw [mounted_incidence_is_source_incidence]
      exact canonical.incidences }

theorem prelayout_rebuild_preserves_bytes_and_pays_actual_phases :
    let addon := installResidentBank X
    let mounted := mountResident X addon.result
    let prior := (nativeIngress X.site parents.result X.canonical fit oldInj).paid
    (rebuildNativeIngress X parents fit oldInj).paid =
      ⟨prior.result,parents.steps+addon.steps+mounted.steps+prior.steps⟩ := by
  unfold rebuildNativeIngress nativeIngress
  dsimp only
  rw [mounted_incidence_is_source_incidence]

theorem copied_addon_tape_has_actual_parent_count :
    X.site.input.length=2*v.parent.edges := by
  have raw := J6R36RouteConservation.real_parent_tape_has_two_records_per_edge T v X.birth.native.physical
  rw [X.birth.native.physical.source,List.length_map] at raw
  rw [X.site.aligned,List.length_map]
  exact raw

theorem actual_prelayout_addon_install_width_cap (K : ℕ)
    (parentSize : v.parent.edges≤K)
    (port : X.birth.port≤K) (own : X.site.ownerWidth≤K)
    (d : dim v≤K) (k : key≤K) (p : prec≤K) (pg : page≤K) :
    (installResidentBank X).steps≤4+(21*K+52)*(2*K) := by
  change X.site.install.steps≤_
  rw [(X.site.install_exact).2]
  apply Nat.add_le_add_left _ 4
  let fee := fun x : Addon X.site.ownerWidth (dim v) key prec page =>
    3*X.birth.port+11+addonFee X.site.ownerWidth (dim v) key prec page x.oldOrigin.pageKey.isSome
  have bound (b : Bool) : 3*X.birth.port+11+
      addonFee X.site.ownerWidth (dim v) key prec page b≤21*K+52 := by
    cases b <;> simp only [addonFee,originFee,Bool.false_eq_true,if_false,if_true] <;> omega
  have sum := sum_mapped_bounded X.site.input fee (21*K+52) (fun x _=>bound x.oldOrigin.pageKey.isSome)
  exact sum.trans (Nat.mul_le_mul_left _ (by rw [copied_addon_tape_has_actual_parent_count]; omega))

variable {gate : ℕ}
-- At the wrapper only layout keys/group values are read, never Gate
-- semantics. The same reader works for the true OwnerData row.
section CompleteInputs
variable (value : v.parent.host.Row⊕v.parent.host.Col→OwnerData gate key prec page)
variable (roster : CompleteRoster X.site.oldKey value)
variable (groups : List (Word 6))
variable (aligned : groups=roster.order.map (fun u=>(ownerGroupRow X.site u).group))

def concreteOwnerIngress :
    Ingress (nativeFull64 X.site (useCompleteRoster X value roster groups aligned).result
      X.canonical fit oldInj) :=
  rebuildNativeIngress X (useCompleteRoster X value roster groups aligned) fit oldInj

theorem exact_owner_inputs_read_is_charged :
    (useCompleteRoster X value roster groups aligned).steps=3+(3*X.site.ownerWidth+25)*roster.order.length :=
  congrArg Meter.steps (actual_group_header_tape X value roster groups aligned)
end CompleteInputs

#print axioms rebuildNativeIngress
#print axioms prelayout_rebuild_preserves_bytes_and_pays_actual_phases
#print axioms actual_prelayout_addon_install_width_cap
#print axioms concreteOwnerIngress
#print axioms exact_owner_inputs_read_is_charged
end
end J6R82LayoutDebit
