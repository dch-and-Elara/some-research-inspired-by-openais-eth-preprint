import J6R94HeldOwnerProviderRosterLayout

/-! Consume the already held original owner bytes and the same
complete greedy result. No name tape is taken as an extra recipe:
actual old names are read from the roster's own physical key fields. -/
namespace J6R94HeldOwnerProvider
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R49SourceLayout
open J6R24MeteredRecursion J6R10Repack J6R11Blueprint J6R12Blueprint J6ActiveRun J1PPrinted
open J6R50SourceProducer J6R34RootAtlas J6R53OldOwner J6R58RequestSource
open J6R82LayoutDebit J6R14LayoutCost J6R68ActiveInputs V8NativeMessage.N2DLabels
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4950
set_option maxHeartbeats 31000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page gwidth : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (Y : StoredSite T v key prec tw bw page)

local instance nativeEdge : Fintype v.parent.host.Edge := v.parent.host.finiteEdge

structure ExistingRosterLabels
    (g : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gwidth)))
    (R : CompleteRoster Y.site.oldKey (parentData Y g))
    (I : CallFormat (printedParams (f:=f) (ell:=ell) s) v.parent)
    (W : Ingress I) (q : ℕ) (raw : GreedyPackedTape) (axisBits : List Bool) : Prop where
  order : R.order=I.order
  cachedLabels : raw.vertexLabels=(runWithIngress I q W).result.vertexLabels
  selectedLabels : I.run.result.2=I.order.map (fun x=>I.format.label (wordsOf (layout T v) x))
  serialized : ∀ x : Fin ((printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth)→Fin 64,
    I.format.label x=coordinateLabel x
  clock : axisBits=Y.input.words.result.axis

def groupHeadersFromOwnedRaw
    (g : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gwidth)))
    (R : CompleteRoster Y.site.oldKey (parentData Y g))
    (I : CallFormat (printedParams (f:=f) (ell:=ell) s) v.parent)
    (W : Ingress I) (q : ℕ) (raw : GreedyPackedTape) (axisBits : List Bool)
    (align : ExistingRosterLabels Y g R I W q raw axisBits) :
    Meter (ParentOwnerHeaders Y.site) :=
  let N := copyActualRosterNames R.raw
  let H := headersFromLiveGreedy Y I W q raw axisBits N.result
    ⟨align.cachedLabels,align.selectedLabels,align.serialized,align.clock,
      (actual_roster_supplies_names_in_its_own_order Y g R).1.trans (congrArg _ align.order)⟩
  ⟨H.result,N.steps+H.steps+4⟩

theorem same_raw_roster_and_actual_labels_supply_true_group_headers
    (g : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gwidth)))
    (R : CompleteRoster Y.site.oldKey (parentData Y g))
    (I : CallFormat (printedParams (f:=f) (ell:=ell) s) v.parent)
    (W : Ingress I) (q : ℕ) (raw : GreedyPackedTape) (axisBits : List Bool)
    (H : ExistingRosterLabels Y g R I W q raw axisBits) :
    let out := groupHeadersFromOwnedRaw Y g R I W q raw axisBits H
    out.result.order=R.order ∧ out.result.raw=I.order.map (ownerGroupRow Y.site) ∧
      out.steps≤3+(3*Y.site.ownerWidth+6)*R.raw.length+
        (3+I.order.length*groupHeaderUnit Y.site.ownerWidth (axis T v).val)+4 := by
  let N := copyActualRosterNames R.raw
  let law : SameRawGroupChart Y I W q raw axisBits N.result := ⟨H.cachedLabels,H.selectedLabels,H.serialized,H.clock,
    (actual_roster_supplies_names_in_its_own_order Y g R).1.trans (congrArg _ H.order)⟩
  have h := genuine_carried_labels_produce_all_grouped_headers Y I W q raw axisBits N.result law
  have budget := (actual_roster_supplies_names_in_its_own_order Y g R).2
  refine ⟨H.order.symm,h.1,?_⟩
  change N.steps+(headersFromLiveGreedy Y I W q raw axisBits N.result law).steps+4≤_
  exact Nat.add_le_add_right (Nat.add_le_add budget.le h.2) 4

#print axioms same_raw_roster_and_actual_labels_supply_true_group_headers
end
end J6R94HeldOwnerProvider