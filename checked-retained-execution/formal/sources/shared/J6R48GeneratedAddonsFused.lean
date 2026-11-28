import J6R48GeneratedAddons

/-! Fuse the paid production and installation passes without materializing
the intermediate addon list. This does not eliminate the installed bank. -/
namespace J6R48GeneratedAddons
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R30ProducedGateRegistry J6ActiveRun J6R24MeteredRecursion
set_option autoImplicit false

def directInstall {X : Type*} {port owner a key prec page : ℕ}
    (address : X → Word port) (readRow : X → Meter (Addon owner a key prec page)) :
    List X → Meter (List (RefRow port (Addon owner a key prec page)))
  | [] => ⟨[],4⟩
  | h::hs =>
    let r := readRow h
    let tag := duplicateWord (address h)
    let payload := copyAddon r.result
    let tail := directInstall address readRow hs
    ⟨⟨tag.result,payload.result⟩::tail.result,r.steps+tag.steps+payload.steps+tail.steps+7⟩

theorem direct_install_exact {X : Type*} {port owner a key prec page : ℕ}
    (address : X → Word port) (readRow : X → Meter (Addon owner a key prec page))
    (order : List X) :
    (directInstall address readRow order).result=order.map (fun h=>⟨address h,(readRow h).result⟩) ∧
      (directInstall address readRow order).steps=4+(order.map (fun h=>(readRow h).steps+
        3*port+11+addonFee owner a key prec page (readRow h).result.oldOrigin.pageKey.isSome)).sum := by
  induction order with
  | nil => exact ⟨rfl,rfl⟩
  | cons h hs ih =>
    simp only [directInstall,duplicate_word_exact,copy_addon_exact,List.map_cons,List.sum_cons,ih.1,ih.2,true_and]
    omega

#print axioms direct_install_exact
end J6R48GeneratedAddons

