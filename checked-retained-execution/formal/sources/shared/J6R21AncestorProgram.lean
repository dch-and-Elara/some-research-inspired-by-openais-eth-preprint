import J6R21AncestorWhole

/-! A whole-source semantic bridge: replacing the native stopping
routine by every supplied executable leaf tape preserves the original
root evaluation. Active assembly remains the original semantic
operation and is not executed or bit-metered by this substitution. -/
namespace J6R21Ancestor
open scoped Polynomial Classical
open A1R10 J6ActiveRun J6R10Reachable J6R12Blueprint J6R11Blueprint J1PPrinted
open J6R18ChildWrite

def replaceLeaf {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    {S : Shape Host Mode} {Val : ℕ→Type*} (p : Program S Val)
    (use : ∀ c : Call Host,Val c.prec) : Program S Val :=
  ⟨p.childHost,p.childEdges,p.edgeBound,use,p.assemble⟩

theorem replaceLeaf_eq_of_eq {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    {S : Shape Host Mode} {Val : ℕ→Type*} (p : Program S Val)
    (use : ∀ c : Call Host,Val c.prec) (h : use=p.leaf) :
    replaceLeaf p use=p := by
  subst use
  cases p
  rfl

variable {f : ℤ[X]} {ell s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic)
variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

set_option maxHeartbeats 1500000 in
noncomputable def leafWords (L : NativeLeafTapes sel r hf) (c : Call (PhysicalHost f ell)) :
    J6R9Recursive.Box f ell c.prec :=
  if h : NativeReach (Plan sel) r c then
    if leaf : c.edges≤(S).cutoff then
      let D := L c h leaf
      castBox D.modulus (uvRead D.hp D.fw ell D.run.result)
    else (sourceBlueprint sel r hf).program.leaf c
  else (sourceBlueprint sel r hf).program.leaf c

set_option maxHeartbeats 1500000 in
theorem leafWords_eq (L : NativeLeafTapes sel r hf) (c : Call (PhysicalHost f ell)) :
    leafWords sel r hf L c=(sourceBlueprint sel r hf).program.leaf c := by
  classical
  unfold leafWords
  split
  · rename_i h
    split
    · rename_i hL
      have e := encoded_leaf_is_source_stop sel r hf L c h hL
      change _=(sourceBlueprint sel r hf).program.run c at e
      have h' : c.edges≤(paddedShape (N sel) (Childs sel) r).cutoff := hL
      rw [Program.run,dif_pos h'] at e
      exact e
    · rfl
  · rfl

noncomputable def paidSource (L : NativeLeafTapes sel r hf) :=
  replaceLeaf (sourceBlueprint sel r hf).program (leafWords sel r hf L)

theorem paidSource_eq (L : NativeLeafTapes sel r hf) :
    paidSource sel r hf L=(sourceBlueprint sel r hf).program :=
  replaceLeaf_eq_of_eq _ _ (funext (leafWords_eq sel r hf L))

theorem paid_source_root (L : NativeLeafTapes sel r hf) :
    (paidSource sel r hf L).run r=(sourceBlueprint sel r hf).program.run r := by
  rw [paidSource_eq]

#print axioms replaceLeaf_eq_of_eq
#print axioms leafWords_eq
#print axioms paidSource_eq
#print axioms paid_source_root
end J6R21Ancestor

