import J6R94HeldOwnerProviderCore
import J6R82LayoutDebitRebuildCap

/-! Consume the live occurrence resident bank and already produced complete owner data. The only new table emitted at the stop is a copy of its real grouped header words. No page publication or roster rebuild occurs here. -/
namespace J6R94HeldOwnerProvider
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
local notation "deg" => (4*Nat.clog 2 s)
local notation "ch" => (p.ticket w).child

open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R36ChildFramedRoute J6R58LeafScale J6R10Repack

variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))

/-- Physical operands of the real local reader; no callback tariff or
    claimed supply correctness occurs among its fields. -/
structure LocalOwnerGeometry (K : ℕ) : Prop where
  parentEdges : c.edges≤K
  childEdges : (p.ticket w).child.edges≤K
  port : Y.birth.port≤K
  owner : Y.site.ownerWidth≤K
  axis : dim (p.ticket w)≤K
  keyWidth : key≤K
  precWidth : prec≤K
  pageWidth : pageKeyWidth m+pad≤K
  body : ∀ h : Port c.host.Edge,(Y.birth.native.physical.record h).body.length≤K

def localOwnerBudget (K V0 : ℕ) : ℕ := 256*(K+1)^3+3+(3*K+26)*V0+5

theorem all_actual_grouped_headers_count_the_parent_vertices
    (headers : ParentOwnerHeaders Y.site) :
    headers.raw.length=vertexCount c.host := by
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  rw [headers.same,List.length_map]
  have e := actual_complete_order_length headers.order headers.unique headers.all
  change headers.order.length=Nat.card (c.host.Row⊕c.host.Col) at e
  exact e.trans (by rw [Nat.card_sum]; rfl)

theorem real_held_owner_provider_has_geometric_fee
    (resident : ResidentBank Y) (headers : ParentOwnerHeaders Y.site)
    (owners : CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p)))
    (injective : Function.Injective Y.site.oldKey)
    {K : ℕ} (widths : LocalOwnerGeometry X p w Y K) :
    (paidHeldOwnerInput X p w Y resident headers owners injective).steps≤
      localOwnerBudget K (vertexCount (ext).host+4*(C*s)) := by
  let install := (installResidentBank Y).result
  have b : resident.rows=install.rows := resident.exactRows.trans install.exactRows.symm
  have same : (mountResident Y resident).steps=(mountResident Y install).steps := by
    rw [mounted_resident_fee,mounted_resident_fee,b]
  have m := independently_priced_pre_layout_mount Y K widths.parentEdges widths.childEdges
    widths.port widths.owner widths.axis widths.keyWidth widths.precWidth widths.pageWidth widths.body
  have count : headers.raw.length≤vertexCount (ext).host+4*(C*s) :=
    (all_actual_grouped_headers_count_the_parent_vertices X p w Y headers).trans_le
      (actual_leaf_field_width_and_vertices (T:=T) p).2.2
  have h := (genuine_held_owner_input_keeps_paid_objects_and_exact_fee X p w Y resident headers owners injective).2.2.2
  rw [h,same]
  have o := Nat.mul_le_mul (show 3*Y.site.ownerWidth+26≤3*K+26 by have := widths.owner; omega) count
  simpa only [localOwnerBudget,Nat.add_assoc] using
    Nat.add_le_add_right (Nat.add_le_add m (Nat.add_le_add_left o 3)) 5

theorem real_rebuilt_owner_provider_has_explicit_upstream_bill
    (resident : ResidentBank Y) (headers : ParentOwnerHeaders Y.site)
    (owners : Meter (CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p))))
    (injective : Function.Injective Y.site.oldKey)
    {K : ℕ} (widths : LocalOwnerGeometry X p w Y K) :
    (paidBuiltOwnerInput X p w Y resident headers owners injective).steps≤
      owners.steps+localOwnerBudget K (vertexCount (ext).host+4*(C*s)) :=
  Nat.add_le_add_left (real_held_owner_provider_has_geometric_fee X p w Y resident headers
    owners.result injective widths) _

#print axioms all_actual_grouped_headers_count_the_parent_vertices
#print axioms real_held_owner_provider_has_geometric_fee
#print axioms real_rebuilt_owner_provider_has_explicit_upstream_bill
end
end J6R94HeldOwnerProvider