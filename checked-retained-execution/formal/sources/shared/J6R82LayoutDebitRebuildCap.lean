import J6R82LayoutDebitRebuild
import J6R57ActiveFeeMount

/-! The independently charged pre-layout frame rebuild has a concrete
dimension cap on the ordinary R52 mount, before the current greedy call.
No coefficient, fee or source-endpoint oracle is used for this cap. -/
namespace J6R82LayoutDebit
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J6R34ChildPath J6R41StructuredAllPaths J6R36ChildFramedRoute
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R48RawRoute J6R34RootAtlas
open J6R49SourceLayout J6R50SourceProducer J6R52CacheWhole J6R51ParentFrames
open J6R68ActiveInputs J6R32ChildResidentTransfer J6R53OldOwner J6R25PreparedSupply
open J6R57ActiveFee J6R36RouteConservation
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
local instance capEdgeFinite : Fintype v.child.host.Edge := v.child.host.finiteEdge

theorem independently_priced_pre_layout_mount (K : ℕ)
    (pn : v.parent.edges≤K) (cn : v.child.edges≤K) (port : X.birth.port≤K)
    (owners : X.site.ownerWidth≤K) (dimension : dim v≤K)
    (kw : key≤K) (pw : prec≤K) (pg : page≤K)
    (bodies : ∀ h : Port v.parent.host.Edge,(X.birth.native.physical.record h).body.length≤K) :
    (mountResident X (installResidentBank X).result).steps≤256*(K+1)^3 := by
  let bank := (installResidentBank X).result
  let file := X.birth.native.physical
  let selected := halfOrder T v file
  let fee := fun h : HalfAt T v=>visitFee X.birth.port X.site.ownerWidth (dim v) key prec page
    bank.rows.length (file.record h.val).body.length (X.site.aux h.val).oldOrigin.pageKey.isSome
  have raw : file.raw.length=2*v.parent.edges := real_parent_tape_has_two_records_per_edge T v file
  have len : bank.rows.length=2*v.parent.edges := by
    rw [bank.exactRows,X.site.bank_exact,List.length_map]
    rw [file.source,List.length_map] at raw
    exact raw
  have fits (x : PortRow X.birth.port) (mem : x∈file.raw) :
      rowScanFee x≤2*X.birth.port+3*K+81 := by
    rw [file.source] at mem
    obtain ⟨h,_,rfl⟩ := List.mem_map.mp mem
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ (bodies h)) _) _
  have sourceScan := map_fee_bound file.raw rowScanFee _ fits
  rw [raw] at sourceScan
  have targetScan := map_fee_bound selected fee
    (visitFee X.birth.port X.site.ownerWidth (dim v) key prec page bank.rows.length K true)
    (fun h _=>visitFee_body_and_presence (bodies h.val) _)
  rw [show selected.length=v.child.edges from half_order_length T v file,len] at targetScan
  have charged := paid_parent_frames_local_cap X.site bank.rows bank.exactRows
  change (paidParentFrames X.site bank.rows).steps≤11+(file.raw.map rowScanFee).sum+(selected.map fee).sum at charged
  have once := mounted_resident_fee X bank
  change (mountResident X bank).steps≤_
  rw [once]
  exact (show (paidParentFrames X.site bank.rows).steps+3+2≤
    frameMountCap v.parent.edges v.child.edges X.birth.port X.site.ownerWidth (dim v) key prec page K by
      unfold frameMountCap
      omega).trans (frameMountCap_polynomial pn cn port owners dimension kw pw pg le_rfl)

def rebuiltIngressRoof (K : ℕ) : ℕ :=
  (3+(3*K+25)*K)+(4+(21*K+52)*(2*K))+256*(K+1)^3+ingressRoof K

variable {gate : ℕ}
variable (value : v.parent.host.Row⊕v.parent.host.Col→OwnerData gate key prec page)
variable (roster : CompleteRoster X.site.oldKey value)
variable (groups : List (Word 6))
variable (aligned : groups=roster.order.map (fun u=>(ownerGroupRow X.site u).group))
variable (fit : v.child.edges<2^q) (oldInj : Function.Injective X.site.oldKey)

theorem actual_prelayout_ingress_fits_widths_including_recomputation
    (K : ℕ)
    (widths : NativeIngressDimensions X.site (useCompleteRoster X value roster groups aligned).result K)
    (pn : v.parent.edges≤K) (dimension : dim v≤K)
    (bodies : ∀ h : Port v.parent.host.Edge,(X.birth.native.physical.record h).body.length≤K) :
    (concreteOwnerIngress X fit oldInj value roster groups aligned).paid.steps≤ rebuiltIngressRoof K := by
  let parents := useCompleteRoster X value roster groups aligned
  let base := nativeIngress X.site parents.result X.canonical fit oldInj
  let addon := installResidentBank X
  let mounted := mountResident X addon.result
  change (rebuildNativeIngress X parents fit oldInj).paid.steps≤_
  have bill := congrArg Meter.steps (prelayout_rebuild_preserves_bytes_and_pays_actual_phases X parents fit oldInj)
  change (rebuildNativeIngress X parents fit oldInj).paid.steps=parents.steps+addon.steps+mounted.steps+base.paid.steps at bill
  rw [bill]
  have census : parents.result.raw.length=roster.order.length := by
    calc
      _=(parents.result.order.map (ownerGroupRow X.site)).length :=
        congrArg List.length parents.result.same
      _=_ := (List.length_map _).trans rfl
  have headCount := widths.parentRows
  change parents.result.raw.length≤K at headCount
  rw [census] at headCount
  have header : parents.steps≤3+(3*K+25)*K := by
    change (useCompleteRoster X value roster groups aligned).steps≤_
    rw [exact_owner_inputs_read_is_charged]
    have h := widths.owner
    exact Nat.add_le_add_left (Nat.mul_le_mul (by omega) headCount) 3
  have a := actual_prelayout_addon_install_width_cap X K pn widths.port widths.owner dimension
    widths.stampKey widths.stampPrecision widths.pageKey
  have m := independently_priced_pre_layout_mount X K pn widths.extent widths.port widths.owner
    dimension widths.stampKey widths.stampPrecision widths.pageKey bodies
  have e := actual_descendant_ingress_fits_width_roof X.site parents.result X.canonical fit oldInj K widths
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add header a) m) e

/-- Exact whole-Meter provenance is the bridge to an already chosen
layout rawDebit, not normalization of an older Meter's byte payload. -/
theorem measured_rawDebit_from_actual_prelayout_rebuild
    (K : ℕ)
    (widths : NativeIngressDimensions X.site (useCompleteRoster X value roster groups aligned).result K)
    (pn : v.parent.edges≤K) (dimension : dim v≤K)
    (bodies : ∀ h : Port v.parent.host.Edge,(X.birth.native.physical.record h).body.length≤K)
    (actual : Meter IngressBytes)
    (isSame : actual=(concreteOwnerIngress X fit oldInj value roster groups aligned).paid) :
    actual.steps≤ rebuiltIngressRoof K := by
  rw [isSame]
  exact actual_prelayout_ingress_fits_widths_including_recomputation X value roster groups aligned
    fit oldInj K widths pn dimension bodies
#print axioms independently_priced_pre_layout_mount
#print axioms actual_prelayout_ingress_fits_widths_including_recomputation
#print axioms measured_rawDebit_from_actual_prelayout_rebuild
end
end J6R82LayoutDebit
