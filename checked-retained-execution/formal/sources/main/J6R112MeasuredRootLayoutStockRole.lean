import J6R112MeasuredRootLayoutStockChart
import J6R19RetainedFrames
import J6R30GeneratedRootLayoutReceipt

/-! No role truth is imported from an arbitrary role array.
For a planted vertex its original role is constant, even if isolated.
For an original padding vertex the first real scoped stable key begins
with the two actual uncompressed cell coordinates. Read the correct
6a-bit half from that already held input. -/
namespace J6R112MeasuredRootLayoutStock
open scoped Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R19Retained
open J6R21Ancestor J6R26DescriptorTree J6R36ChildFramedRoute
open J6OrientedHost J6Mesh J6R10Repack J6R11Repack J6R21Leaf
open J6R14LayoutCost J6R24LegalLayout J6R28GeneratedRootFrame
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R53OldOwnerRoot J6R54ExteriorOwner

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 4600000
set_option maxRecDepth 4400
set_option Elab.async false
noncomputable section

def readCellRole (w : ℕ) (right : Bool) (raw : List Bool) : Meter BootRole :=
  let left := cutWord w raw
  if right then
    let r := cutWord w left.result.2
    ⟨BootRole.padding r.result.1.val,left.steps+r.steps+4⟩
  else
    ⟨BootRole.padding left.result.1.val,left.steps+3⟩

theorem read_role_from_two_exact_cell_words {w : ℕ}
    (left right : A1R10.Word w) (suffix : List Bool) (side : Bool) :
    (readCellRole w side (left.val++(right.val++suffix))).result=
      BootRole.padding (if side then right.val else left.val) := by
  have dl := cutWord_exact left (right.val++suffix)
  have dr := cutWord_exact right suffix
  cases side
  · unfold readCellRole
    simp only [dl.1,dl.2,Bool.false_eq_true,if_false]
  · unfold readCellRole
    simp only [dl.1,dl.2,dr.1,dr.2,if_true]

variable {V : Type} [Fintype V] {m n : ℕ}
variable (P : Plant V m n)
local notation "U" => (SourceVertex P)
local notation "W" => (constantRootWord m)
local notation "DCell" => (J6OrientedHost.Pad (constantRootWord m) m (K m) (printedHalf m))

def roleFromActualScopes (u : U) (scopes : List (Word (SuffixKeyWidth m))) : Meter BootRole :=
  if isPadding P u then
    match scopes with
    | [] => ⟨BootRole.padding [],4⟩
    | key::_ =>
      let out := readCellRole (6*a m) (ownerSide P u) key.bits
      ⟨out.result,out.steps+4⟩
  else
    ⟨BootRole.planted,4⟩

theorem padding_stable_scope_contains_the_two_original_axes (p : DCell) (b side : Bool) :
    (readCellRole (6*a m) side ((stableWireKeyWord m (.inr (p,b))).bits)).result=
      BootRole.padding (if side then coordinateLabel (fun i=>(p.1 i).2)
        else coordinateLabel (fun i=>(p.1 i).1)) := by
  let left : A1R10.Word (6*a m) := ⟨coordinateLabel (fun i=>(p.1 i).1),coordinateLabel_len _⟩
  let right : A1R10.Word (6*a m) := ⟨coordinateLabel (fun i=>(p.1 i).2),coordinateLabel_len _⟩
  let rem := encodeBits (printedRankWidth m) (rankAt m (.inr (p,b))).2.val
  change (readCellRole (6*a m) side (left.val++(right.val++rem))).result=_
  exact read_role_from_two_exact_cell_words left right rem side

theorem the_original_scope_plan_produces_true_role
    {own rank key prec page : ℕ} (name : U→Word own) (origin : U→Origin key prec page)
    (choice : U→HeadChoice rank) (u : U) :
    (roleFromActualScopes P u (rootPlanWord P name origin choice u).scopes).result=trueRootRole u := by
  rcases u with ((⟨v,k⟩|⟨p,b⟩)|(⟨v,k⟩|p))
  · rfl
  · change (readCellRole (6*a m) false (stableWireKeyWord m (.inr (p,b))).bits).result=
      BootRole.padding (coordinateLabel (fun i=>(p.1 i).1))
    exact padding_stable_scope_contains_the_two_original_axes (m:=m) p b false
  · rfl
  · change (readCellRole (6*a m) true (stableWireKeyWord m (.inr (p,false))).bits).result=
      BootRole.padding (coordinateLabel (fun i=>(p.1 i).2))
    exact padding_stable_scope_contains_the_two_original_axes (m:=m) p false true

#print axioms read_role_from_two_exact_cell_words
#print axioms padding_stable_scope_contains_the_two_original_axes
#print axioms the_original_scope_plan_produces_true_role
end
end J6R112MeasuredRootLayoutStock

