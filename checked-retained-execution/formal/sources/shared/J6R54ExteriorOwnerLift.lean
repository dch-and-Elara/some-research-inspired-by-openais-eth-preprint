import J6R54ExteriorOwnerWords

/-! Small sum-type combinator so the dependence on the actual physical
root chart need not be unfolded to specialize the raw writer. -/
namespace J6R54ExteriorOwner
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R53OldOwner J6R36ChildFramedRoute J6R26DescriptorTree
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
set_option Elab.async false

theorem checked_mount_words_as_given_data {U V : Type} {f : ℤ[X]}
    {ell key prec tw bw page own gate next : ℕ}
    (bank : PageBank f ell key prec tw bw page) (creator : Word key) (group : Word 6)
    (headers : List (OwnerGroup own)) (root : RawRoster own gate key prec page)
    (dest : Meter (List (Word next))) (stamp : Stamp key prec)
    (pageWord : V→Word page) (name : U⊕V→Word next) (data : U⊕V→OwnerData gate key prec page)
    (us : List U) (vs : List V)
    (born : ∀ k,data (.inr k)=freshOwnerData stamp (pageWord k))
    (oldSame : (gatherOwners root (selectOwnerKeys group headers).result).result=
      some (us.map (fun u=>data (.inl u))))
    (pagesSame : (readMountedOwners bank creator).result=some (stamp,vs.map pageWord))
    (keySame : dest.result=(us.map Sum.inl ++ vs.map Sum.inr).map name) :
    (mountWords bank creator group headers root dest).result=
      some ((us.map Sum.inl++vs.map Sum.inr).map (fun u=>⟨name u,data u⟩)) := by
  let n₁ := fun u=>name (.inl u)
  let n₂ := fun k=>name (.inr k)
  let v₁ := fun u=>data (.inl u)
  let v₂ := fun k=>freshOwnerData (gate:=gate) stamp (pageWord k)
  have names : (Sum.elim n₁ n₂ : U⊕V→Word next)=name := by
    funext x
    cases x <;> rfl
  have vals : (Sum.elim v₁ v₂ : U⊕V→OwnerData gate key prec page)=data := by
    funext x
    cases x with
    | inl u=>rfl
    | inr k=>exact (born k).symm
  have keys : dest.result=(us.map Sum.inl ++ vs.map Sum.inr).map (Sum.elim n₁ n₂) := by
    rw [names]
    exact keySame
  have q := congrArg Meter.result
    (mount_words_from_actual_reads bank creator group headers root dest stamp pageWord v₁ n₁ n₂ us vs
      oldSame pagesSame keys)
  change (mountWords bank creator group headers root dest).result=
    some ((us.map Sum.inl++vs.map Sum.inr).map
      (fun x=>⟨Sum.elim n₁ n₂ x,Sum.elim v₁ v₂ x⟩)) at q
  rw [names,vals] at q
  exact q

#print axioms checked_mount_words_as_given_data
end J6R54ExteriorOwner
