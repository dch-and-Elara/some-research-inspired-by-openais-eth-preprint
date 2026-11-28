import J6R48LeafExecution
import J6R33StatefulArithmeticPageWhole
import J6R21LeafBudgetBind

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13000000
set_option maxRecDepth 2450

/-! One actual source stopping branch and, in particular, an addressed
child of the same Plan. The cost comes from the raw installed leaf
codes, not from a supplied U or completed result. The resident program
still carries its existing source port-correctness contract. -/
namespace J6R48Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6ActiveRun J6R9Recursive J6R10Reachable J6R10Repack J6R11Blueprint
open J6R12Blueprint J6R16ModeCost J1PPrinted
open J6R21Leaf J6R22Active J6R24MeteredRecursion J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "Bnk" => PageBank f ell key prec tw bw page
variable {T : Prepared cfg sel root hf}
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) root)]
variable (R : PagedResident T key prec tw bw page)

theorem raw_resident_leaf_vertex_count {c : Call (PhysicalHost f ell)}
    (path : Path sel root c) (stop : c.edges≤(S).cutoff) :
    (PagedLeaf.toRaw (R.leaf path stop)).rows.length≤vertexCount root.host+4*root.edges := by
  let D := R.leaf path stop
  change (D.nodes.map (fun v=>(v,D.route v))).length≤_
  rw [List.length_map,complete_vertex_list_length c.host D.nodes D.unique D.complete]
  exact native_vertex_cap cfg sel path.reached T.rootStable

theorem paid_reached_source_leaf {c : Call (PhysicalHost f ell)}
    (path : Path sel root c) (stop : c.edges≤(S).cutoff)
    (B : Bnk) (live : opened R.births R.rootLive path B)
    (format : HasResidentFormat (PagedLeaf.toRaw (R.leaf path stop)) B) :
    let F := T.frame path.reached
    let data := PagedLeaf.toRaw (R.leaf path stop)
    let value := nativePaged R c path B
    F.decode value.result.1=(sourceBlueprint sel root hf).program.run c ∧
      value.result.2=B ∧
      value.steps≤rawLeafCap F.words.length ell c.prec (S).cutoff
        (vertexCount root.host+4*root.edges) (prepriced data F B) F.hp := by
  let F := T.frame path.reached
  let D := R.leaf path stop
  let data := PagedLeaf.toRaw D
  have x:= raw_leaf_is_same_dispatch D hf F T.vPositive B
  have fee := raw_leaf_steps data hf F T.vPositive B format
  change (runTape data hf F T.vPositive B).steps≤_ at fee
  rw [show runTape data hf F T.vPositive B=D.execute hf F T.vPositive B from x] at fee
  have out := live_paged_leaf_source R path stop B live
  dsimp only
  rw [paged_leaf R path stop B]
  dsimp only
  exact ⟨out,rfl,fee.trans (raw_leaf_cap_mono _ _ _ _ F.hp stop (raw_resident_leaf_vertex_count R path stop))⟩

set_option maxHeartbeats 15500000 in
theorem paid_exact_addressed_child_leaf {c : Call (PhysicalHost f ell)}
    (path : Path sel root c) (slot : (Plan sel).Slot c)
    (stop : ((Plan sel).child c slot).edges≤(S).cutoff) (B : Bnk)
    (live : opened R.births R.rootLive (Path.step path slot) B)
    (format : HasResidentFormat (PagedLeaf.toRaw (R.leaf (Path.step path slot) stop)) B) :
    let leaf := (Plan sel).child c slot
    let current := (Path.step path slot).reached
    let F := T.frame current
    let code := PagedLeaf.toRaw (R.leaf (Path.step path slot) stop)
    let out := nativePaged R leaf (.step path slot) B
    F.decode out.result.1 = (sourceBlueprint sel root hf).program.run leaf ∧
      out.result.2=B ∧
      out.steps≤rawLeafCap F.words.length ell leaf.prec (S).cutoff
        (vertexCount root.host+4*root.edges) (prepriced code F B) F.hp :=
  paid_reached_source_leaf R (.step path slot) stop B live format

#print axioms raw_resident_leaf_vertex_count
#print axioms paid_reached_source_leaf
#print axioms paid_exact_addressed_child_leaf
end J6R48Leaf
