import J6R37StructuredRootFields
import J6R48RawRouteFrame

/-! The exterior ordered edge list comes from the original checked
root half-port filter. The actual boot writer can consume the already
resident root tape, without publishing a second copy of the seed
and without guessing a lineage body. -/
namespace J6R55BootBodies
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R48RawRoute
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18500000
set_option maxRecDepth 3500
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => ((Ext).host.Edge)

def exteriorKeep (h : Port (RootWire m)) : Prop :=
  physicalGroup (G.selector ell) (G.ready ell) (G.centre ell X.centre) h=X.group

def exteriorKeepDec (h : Port (RootWire m)) : Decidable (exteriorKeep X h) :=
  inferInstanceAs (Decidable (physicalGroup (G.selector ell) (G.ready ell) (G.centre ell X.centre) h=X.group))

def orderedExteriorEdges : List E :=
  @scanSubtype _ (exteriorKeep X) (exteriorKeepDec X) (rootParent X).order

theorem reviewed_exterior_order : (orderedExteriorEdges X).Nodup ∧ ∀ h : E,h∈orderedExteriorEdges X := by
  refine ⟨@scan_subtype_nodup _ (exteriorKeep X) (exteriorKeepDec X) (rootParent X).order (rootParent X).nodup,?_⟩
  intro h
  exact (@scan_subtype_mem _ (exteriorKeep X) (exteriorKeepDec X) (rootParent X).order h).mpr
    ((rootParent X).complete h.val)

private theorem selected_subtype_is_filter {A : Type} (p : A→Prop) [DecidablePred p] (xs : List A) :
    (xs.filter (fun x=>decide (p x)))=(scanSubtype p xs).map Subtype.val := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    unfold scanSubtype at *
    by_cases h : p x
    · simp only [List.filter_cons,List.filterMap_cons,decide_eq_true h,if_true,dif_pos h,List.map_cons,ih]
    · simp only [List.filter_cons,List.filterMap_cons,decide_eq_false h,Bool.false_eq_true,if_false,dif_neg h,ih]

theorem exterior_order_is_exactly_selected :
    (rootParent X).physicalSelected X.group=(orderedExteriorEdges X).map Subtype.val := by
  calc
    (rootParent X).physicalSelected X.group =
        (rootParent X).order.filter (fun p=>@decide (exteriorKeep X p) (exteriorKeepDec X p)) := by
      unfold PhysicalPorts.physicalSelected
      apply List.filter_congr
      intro p _
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rfl
    _ = _ := @selected_subtype_is_filter _ (exteriorKeep X) (exteriorKeepDec X) (rootParent X).order

#print axioms reviewed_exterior_order
#print axioms exterior_order_is_exactly_selected
end
end J6R55BootBodies
