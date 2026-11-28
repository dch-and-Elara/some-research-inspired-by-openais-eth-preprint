import J6R58LeafScaleExtraLines

/-! A finite nonvacuity check: the exact same valid generated source
command at fixed one-bit widths has arbitrarily costly preparation. -/
namespace J6R58LeafScale
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R33StatefulArithmeticPage J6R50Leaf J6R27OriginalGate
open J6R36ChildFramedRoute J6R26DescriptorTree J6R34ChildPath
set_option autoImplicit false
set_option warningAsError true

def zeroOwner : Word 1 := word 0
def oneOwner : Word 1 := word 1
def fixedStamp : Stamp 1 1 := ⟨zeroOwner,oneOwner⟩
def fixedPageOrigin : PageOrigin 1 1 1 := ⟨⟨fixedStamp,some zeroOwner⟩,[]⟩
def fixedOwnerTable : OriginTable 1 1 1 1 1 := [⟨zeroOwner,.paged fixedPageOrigin⟩]
def fixedExtraLine : ResidentPort 1 1 := ⟨oneOwner,⟨oneOwner,[]⟩⟩
def fixedRead : PageReadCode 1 1 1 := .generated zeroOwner zeroOwner 0 []
def fixedWireAt (_ : Fin 1) : Word 1 := oneOwner

theorem certified_fixed_width_example :
    SourceCommand 1 fixedWireAt [] fixedOwnerTable zeroOwner fixedRead := by
  change SourceCommand 1 fixedWireAt [] fixedOwnerTable zeroOwner
    (.generated fixedStamp.creator zeroOwner fixedPageOrigin.clock.length [])
  let A : HasEntry fixedOwnerTable zeroOwner (.paged fixedPageOrigin) := by
    constructor
    · exact List.mem_cons_self
    · intro r h _
      obtain rfl := List.mem_singleton.mp h
      rfl
  exact .paged fixedPageOrigin fixedStamp zeroOwner ([] : List Unit) (fun _=>[])
    (fun _=>0) rfl A rfl

theorem fixed_width_preparation_counterexample (bound : ℕ) :
    ∃ n : ℕ,
      SourceCommand 1 fixedWireAt (addUnused fixedExtraLine n []) fixedOwnerTable zeroOwner fixedRead ∧
      let paid := buildOwner 1 1 (List.ofFn fixedWireAt) (addUnused fixedExtraLine n []) fixedOwnerTable zeroOwner
      paid.result=some (eraseCode fixedRead) ∧ bound<paid.steps := by
  have miss : zeroOwner≠fixedExtraLine.address := by
    intro s
    have z : zeroOwner.val=0 := by
      change (word (q:=1) 0).val=0
      exact word_val (by decide)
    have o : fixedExtraLine.address.val=1 := by
      change (word (q:=1) 1).val=1
      exact word_val (by decide)
    exact (by decide : (0:ℕ)≠1) (z.symm.trans ((congrArg Word.val s).trans o))
  have hit : (locate zeroOwner fixedOwnerTable).result=some (.paged fixedPageOrigin) := by
    apply locate_hit
    · exact List.mem_cons_self
    · intro r h _
      obtain rfl := List.mem_singleton.mp h
      rfl
  obtain ⟨n,_,fee⟩ :=
    one_selected_page_owner_has_no_uniform_fee (N:=1) (b:=1)
      (List.ofFn fixedWireAt) zeroOwner fixedExtraLine miss [] fixedOwnerTable fixedPageOrigin zeroOwner hit rfl bound
  have good := unused_resident_lines_keep_source_command fixedWireAt zeroOwner fixedExtraLine
    miss n [] fixedOwnerTable certified_fixed_width_example
  exact ⟨n,good,real_source_command_is_bought (by decide) _ fixedWireAt
    (fun _ _ _=>Subsingleton.elim _ _) rfl _ _ _ good,fee⟩

#print axioms certified_fixed_width_example
#print axioms fixed_width_preparation_counterexample
end J6R58LeafScale
