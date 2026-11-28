import J6R36ChildFramedRouteBatch

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000

/-! Optional paid installation of the structured lookup sidecar from
two already aligned original parent files. The alignment theorem
explicitly names the *same* R26 order; no proof-produced reordering
is moved into the bit program. -/
namespace J6R36ChildFramedRoute
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion

def copyAddon {owner a key prec page : ℕ} (x : Addon owner a key prec page) :
    Meter (Addon owner a key prec page) :=
  let own := duplicateWord x.oldOwner
  let prior := copyOrigin x.oldOrigin
  let slot := duplicateWord x.parentSlot
  let pg := duplicateWord x.newPage
  ⟨⟨own.result,prior.result,x.parentWasCol,slot.result,pg.result⟩,
    own.steps+prior.steps+slot.steps+pg.steps+7⟩

def addonFee (owner a key prec page : ℕ) (present : Bool) :=
  3*owner+3*a+3*page+originFee key prec page present+19

theorem copy_addon_exact {owner a key prec page : ℕ} (x : Addon owner a key prec page) :
    copyAddon x=⟨x,addonFee owner a key prec page x.oldOrigin.pageKey.isSome⟩ := by
  cases x
  simp only [copyAddon,duplicate_word_exact,copy_origin_exact,addonFee]
  congr 1
  dsimp only
  omega

def installAddons {w owner a key prec page : ℕ} :
    List (PortRow w)→List (Addon owner a key prec page)→
      Meter (Option (List (RefRow w (Addon owner a key prec page))))
  | [],[]=>⟨some [],4⟩
  | [],_::_=>⟨none,4⟩
  | _::_,[]=>⟨none,4⟩
  | p::ps,b::bs=>
    let tag := duplicateWord p.address
    let row := copyAddon b
    let tail := installAddons ps bs
    ⟨tail.result.map (⟨tag.result,row.result⟩::·),tag.steps+row.steps+tail.steps+7⟩

theorem installed_addons_exact {X : Type*} {w owner a key prec page : ℕ}
    (ports : List X) (record : X→PortRow w) (data : X→Addon owner a key prec page) :
    let run := installAddons (ports.map record) (ports.map data)
    run.result=some (ports.map (fun p=>⟨(record p).address,data p⟩)) ∧
      run.steps=4+(ports.map (fun p=>3*w+11+addonFee owner a key prec page
        (data p).oldOrigin.pageKey.isSome)).sum := by
  induction ports with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨value,fee⟩ := ih
    simp only [List.map_cons,installAddons,duplicate_word_exact,copy_addon_exact,
      value,fee,Option.map_some,List.sum_cons,true_and]
    omega

variable {f : ℤ[X]} {ell s C w ownerW key prec page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

theorem prepared_addons_exact_for_same_source
    (D : PhysicalPorts sel (ticketReady T v) v.centerAt w)
    (ownerKey : v.parent.host.Row⊕v.parent.host.Col→Word ownerW)
    (ancestor : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page)
    (pageKey : PageAt T v→Word page)
    (input : List (Addon ownerW (dim v) key prec page))
    (coherent : input=D.order.map (addonAt T v ownerKey ancestor pageKey)) :
    let run := installAddons D.raw input
    run.result=some (D.order.map (fun h=>⟨(D.record h).address,addonAt T v ownerKey ancestor pageKey h⟩)) ∧
      run.steps=4+(input.map (fun p=>3*w+11+addonFee ownerW (dim v) key prec page
        p.oldOrigin.pageKey.isSome)).sum := by
  rw [D.source,coherent]
  have H := installed_addons_exact D.order D.record (addonAt T v ownerKey ancestor pageKey)
  simpa only [List.map_map,Function.comp_def] using H

#print axioms copy_addon_exact
#print axioms installed_addons_exact
#print axioms prepared_addons_exact_for_same_source
end J6R36ChildFramedRoute
