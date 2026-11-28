import J6R94HeldOwnerProviderHeaders
import J6R82LayoutDebitNative
import J6R58RequestSourceOwners

/-! Use the actual regenerated/current complete roster's owner key
fields. The layout and the original owner producer both use the
same retained-row/birth-page order, not arbitrary permutations. -/
namespace J6R94HeldOwnerProvider
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R49SourceLayout
open J6R24MeteredRecursion J6R52CacheSource J6R10Repack J6R11Blueprint J6R12Blueprint J6ActiveRun J1PPrinted
open J6R50SourceProducer J6R34RootAtlas J6R53OldOwner J6R58RequestSource
open J6R82LayoutDebit J6R14LayoutCost J6R68ActiveInputs V8NativeMessage.N2DLabels
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 26000000
set_option Elab.async false

def copyActualRosterNames {own : ℕ} {G : Type} : List (RefRow own G)→Meter (List (Word own))
  | []=>⟨[],3⟩
  | r::rs=>
    let k := copyFixed r.address
    let tail := copyActualRosterNames rs
    ⟨k.result::tail.result,k.steps+tail.steps+5⟩

theorem copying_true_roster_names_exact {own : ℕ} {G : Type} (raw : List (RefRow own G)) :
    copyActualRosterNames raw=⟨raw.map RefRow.address,3+(3*own+6)*raw.length⟩ := by
  induction raw with
  | nil => rfl
  | cons x xs ih =>
    simp only [copyActualRosterNames,copy_fixed_exact,ih,List.map_cons,List.length_cons]
    congr 1
    ring

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q gate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (Y : StoredSite T v key prec tw bw page)

theorem actual_roster_supplies_names_in_its_own_order
    (g : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gate)))
    (R : CompleteRoster Y.site.oldKey (parentData Y g)) :
    (copyActualRosterNames R.raw).result=R.order.map Y.site.oldKey ∧
      (copyActualRosterNames R.raw).steps=3+(3*Y.site.ownerWidth+6)*R.raw.length := by
  rw [copying_true_roster_names_exact]
  refine ⟨?_,rfl⟩
  rw [R.exactRows,List.map_map]
  rfl

local instance forChild : Fintype v.child.host.Edge := v.child.host.finiteEdge
local instance rowsChild : Fintype v.child.host.Row := v.child.host.finiteRow
local instance colsChild : Fintype v.child.host.Col := v.child.host.finiteCol

theorem real_next_layout_and_retained_roster_have_identical_order
    (g : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gate)))
    (R : CompleteRoster Y.site.oldKey (parentData Y g))
    (H : ParentOwnerHeaders Y.site) (inj : Function.Injective Y.site.oldKey)
    (fit : v.child.edges<2^q) :
    (nativeFull64 Y.site H Y.canonical fit inj).order=(openCurrentOwners Y g R H inj).result.order := rfl

#print axioms copying_true_roster_names_exact
#print axioms actual_roster_supplies_names_in_its_own_order
#print axioms real_next_layout_and_retained_roster_have_identical_order
end
end J6R94HeldOwnerProvider