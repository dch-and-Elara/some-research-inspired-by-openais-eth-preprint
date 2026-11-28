import J6R111KeptOwnerFlowRun
import J6R82LayoutDebitRebuildCap
import J6R94HeldOwnerProviderUniform

/-! Count the one actual parent header scan before the selected layout,
and the actual resident mount at that same invocation. -/
namespace J6R116RetainedPrefix
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R49Leaf J6R57Public J6R49Cost

open J6R21Leaf J6R52Peak J6R111KeptOwnerFlow J6R57ActiveFee J6R67UnifiedRate J6R58LeafScale J6R50Peak
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 39000000
set_option maxRecDepth 5600
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : KeptDrivers X M rank)
variable (x : KeptInvocation X M)


def groupHeadScanRoof (K V₀ : ℕ) : ℕ :=
  3+(3*K+6)*V₀+(3+V₀*groupHeaderUnit K K)+4

theorem actual_retained_parent_headers_pay_one_true_roster_scan
    (K : ℕ) (geo : LocalOwnerGeometry X x.path x.slot x.site K) :
    (readGroupHeadersForActive X x.path x.slot x.site x.entry).steps≤
      groupHeadScanRoof K (vertexCount (exteriorChild G ell X.centre X.sample X.group).host+4*(C*s)) := by
  let Y := x.site
  let A := x.entry
  let W := A.labelled
  letI : Fintype x.parent.host.Edge := x.parent.host.finiteEdge
  let V₀ := vertexCount (exteriorChild G ell X.centre X.sample X.group).host+4*(C*s)
  have size := complete_vertex_list_length x.parent.host A.owners.order A.owners.unique A.owners.complete
  have v := (actual_leaf_field_width_and_vertices (T:=T) x.path).2.2
  have Rlen : A.owners.raw.length≤V₀ := by
    rw [A.owners.exactRows,List.length_map,size]
    exact v
  have Wlen : W.input.order.length≤V₀ := by
    rw [←W.law.order,size]
    exact v
  have ix : (axis T (x.path.ticket x.slot)).val≤K :=
    (axis T (x.path.ticket x.slot)).isLt.le.trans geo.axis
  have raw := (same_raw_roster_and_actual_labels_supply_true_group_headers Y
    (gateHistory T (bootGates X) x.path) A.owners W.input W.ingress W.units W.raw.rawView W.axis W.law).2.2
  have owner : Y.site.ownerWidth≤K := geo.owner
  have a := Nat.mul_le_mul
    (show 3*Y.site.ownerWidth+6≤3*K+6 by omega) Rlen
  have b := Nat.mul_le_mul Wlen (physical_group_header_unit_is_monotone owner ix)
  change _≤groupHeadScanRoof K V₀
  exact raw.trans (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left a 3) (Nat.add_le_add_left b 3)) 4)

theorem actual_retained_resident_mount_has_its_real_word_roof
    (K : ℕ) (geo : LocalOwnerGeometry X x.path x.slot x.site K) :
    (mountResident x.site x.entry.resident).steps≤256*(K+1)^3 := by
  let Y := x.site
  let R := (installResidentBank Y).result
  let A := x.entry.resident
  have same : A.rows=R.rows := A.exactRows.trans R.exactRows.symm
  have paid : (mountResident Y A).steps=(mountResident Y R).steps := by
    rw [mounted_resident_fee,mounted_resident_fee,same]
  rw [show (mountResident x.site x.entry.resident).steps=(mountResident Y A).steps from rfl,paid]
  exact independently_priced_pre_layout_mount Y K geo.parentEdges geo.childEdges geo.port
    geo.owner geo.axis geo.keyWidth geo.precWidth geo.pageWidth geo.body

#print axioms actual_retained_parent_headers_pay_one_true_roster_scan
#print axioms actual_retained_resident_mount_has_its_real_word_roof
end
end J6R116RetainedPrefix
