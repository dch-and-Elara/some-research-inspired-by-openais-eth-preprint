import J6R53PeakAddonLifecycle

/-! The raw list is a concrete field, but its value is determined by
the other typed source fields. Consequently structural equality of
StoredSite cannot prove that the list must be retained in memory.
This recipe does not price recomputation; it is a semantic boundary
for any proposal to erase or share the list. -/
namespace J6R54PeakInput
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R34ChildPath
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R36ChildFramedRoute J6R41StructuredAllPaths J6R50SourceProducer J6R51Online
open J6R51ParentFrames J6R52CacheWhole J6R53PeakAddon

set_option autoImplicit false
set_option maxRecDepth 3700
set_option maxHeartbeats 18500000
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {B : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)

structure RawRecipe (T : Prepared cfg sel r hf) (v : Ticket sel r) (page : ℕ) where
  ownerWidth : ℕ
  oldKey : v.parent.host.Row⊕v.parent.host.Col→Word ownerWidth
  pageKey : PageAt T v→Word page

def forgetRawAddonData (S0 : SiteInputs B previous) : RawRecipe T v page :=
  ⟨S0.ownerWidth,S0.oldKey,S0.pageKey⟩

def reconstructRawAddonData (B : Birth T v key prec tw bw page)
    (previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page)
    (recipe : RawRecipe T v page) : SiteInputs B previous :=
  ⟨recipe.ownerWidth,recipe.oldKey,recipe.pageKey,
    B.native.physical.order.map (addonAt T v recipe.oldKey previous recipe.pageKey),rfl⟩

theorem exact_source_data_are_determined_by_the_recipe (S0 : SiteInputs B previous) :
    reconstructRawAddonData B previous (forgetRawAddonData S0)=S0 := by
  cases S0 with
  | mk ow own pages values exactValues =>
    subst values
    rfl

def reconstructStoredAddonField (X : StoredSite T v key prec tw bw page) :
    StoredSite T v key prec tw bw page :=
  ⟨X.input,X.origins,reconstructRawAddonData X.birth X.origins (forgetRawAddonData X.site),X.canonical⟩

theorem reconstructed_raw_field_is_the_same_source_state (X : StoredSite T v key prec tw bw page) :
    reconstructStoredAddonField X=X := by
  cases X with
  | mk geometry origins site canonical =>
    cases site with
    | mk ow own pages values exactValues =>
      subst values
      rfl

theorem callback_result_and_meter_after_reconstruction_are_equal
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) (w : (P).Slot c)
    (X : StoredSite T (p.ticket w) key prec tw bw page)
    (a : (S).cutoff<((P).child c w).edges) :
    M.activeAfter p w (reconstructStoredAddonField X) a=M.activeAfter p w X a :=
  congrArg (fun Y=>M.activeAfter p w Y a) (reconstructed_raw_field_is_the_same_source_state X)

#print axioms exact_source_data_are_determined_by_the_recipe
#print axioms reconstructed_raw_field_is_the_same_source_state
#print axioms callback_result_and_meter_after_reconstruction_are_equal
end
end J6R54PeakInput
