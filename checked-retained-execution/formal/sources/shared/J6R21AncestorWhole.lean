import J6R21LeafClock
import J6R21LeafBudgetBind
import J6R17ModeTapeSupply
import J6R21AncestorRun

/-! Whole printed run with a tape-supplied leaf interpreter. The
semantic replacement leaves the source program unchanged. The cost
ledger includes the R17 produced-mode stream and the literal clocked
leaf interpreter with every actual entry callback charged. It excludes
constructing the supplied input/descendant tapes, active assembly and
root decoding; none of those receives an invented zero charge. -/
namespace J6R21Ancestor
open scoped BigOperators Classical Polynomial
open AOracleMachineTime A1R10 A1R11 A1R12
open J6ActiveRun J6R10Reachable J6R12Blueprint J6R11Blueprint J6R10Repack
open J1PPrinted J6R16ModeCost J6R17ModeTape J6R21Leaf J6R18ChildWrite

structure EncodedLeaf {f : ℤ[X]} {ell : ℕ} (hf : f.Monic)
    (c : Call (PhysicalHost f ell)) where
  hp : 0<c.prec
  fw : List (A1R10.Word c.prec)
  he : 0<fw.length
  hv : 0<ell
  modulus : Modulus c.prec hp fw=NativeProbeRing.liftPoly c.prec f
  sameEdges : c.host.edgeCount=c.edges
  clock : List Unit
  clockShape : clock.length=c.edges
  nodes : List (c.host.Row⊕c.host.Col)
  hn : nodes.Nodup
  hall : ∀ v,v∈nodes
  query : (c.host.Row⊕c.host.Col)→List Bool→Meter (UVBlock fw ell)
  exactQuery : ∀ (x : Fin c.edges→Bool) v,
    castBox modulus (uvRead hp fw ell (query v (List.ofFn x)).result)=
      (c.host.file v).read hf c.prec (assignment c.host.network (x∘c.host.edgeOrder c.edges sameEdges) v)

variable {f : ℤ[X]} {ell : ℕ} {hf : f.Monic} {c : Call (PhysicalHost f ell)}

def EncodedLeaf.run (D : EncodedLeaf hf c) : Meter (UVBlock D.fw ell) :=
  clockDFS D.hp (readProduct D.hp D.he D.hv D.nodes D.query) D.clock []

theorem EncodedLeaf.run_eq (D : EncodedLeaf hf c) :
    D.run=leafCompute D.hp D.he D.hv c.edges D.nodes D.query :=
  clocked_leaf_is_native_enumerator D.hp D.he D.hv D.nodes D.query D.clock D.clockShape

noncomputable def EncodedLeaf.directBill (D : EncodedLeaf hf c) : ℕ :=
  leafEntryBill c.edges D.nodes D.query

def EncodedLeaf.arithmeticCap (D : EncodedLeaf hf c) : ℕ :=
  2^c.edges*(uvWidth D.fw.length ell c.prec+D.nodes.length*(mulCap D.fw.length ell c.prec+2)
    +reverseFee c.edges)+(2^c.edges-1)*innerFee D.fw.length ell c.prec D.hp

theorem EncodedLeaf.bill (D : EncodedLeaf hf c) :
    D.directBill≤D.run.steps ∧ D.run.steps≤D.directBill+D.arithmeticCap := by
  rw [D.run_eq]
  simpa only [EncodedLeaf.directBill,EncodedLeaf.arithmeticCap,Nat.add_assoc] using
    leafCompute_bills_every_entry D.hp D.he D.hv c.edges D.nodes D.query

variable {s C : ℕ} (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hm : f.Monic)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

abbrev NativeLeafTapes :=
  ∀ (c : Call (PhysicalHost f ell)), NativeReach (Plan sel) r c→c.edges≤(S).cutoff→EncodedLeaf hm c

variable [DecidableEq (Envelope (N sel) (Childs sel) r)] in
theorem encoded_leaf_is_source_stop (L : NativeLeafTapes sel r hm)
    (c : Call (PhysicalHost f ell)) (walk : NativeReach (Plan sel) r c) (leaf : c.edges≤(S).cutoff) :
    let D := L c walk leaf
    castBox D.modulus (uvRead D.hp D.fw ell D.run.result)=(sourceBlueprint sel r hm).program.run c := by
  let D := L c walk leaf
  change castBox D.modulus (uvRead D.hp D.fw ell D.run.result) = _
  rw [D.run_eq]
  exact actual_leaf_is_printed_stop sel r c hm leaf D.hp D.he D.hv D.modulus D.sameEdges D.nodes D.hn D.hall
    D.query D.exactQuery

section Ledger
noncomputable def leafComponent (L : NativeLeafTapes sel r hm)
    (k : (c : Call (PhysicalHost f ell))→EncodedLeaf hm c→ℕ) (c : Call (PhysicalHost f ell)) : ℕ :=
  if hc : NativeReach (Plan sel) r c then
    if hL : c.edges≤(S).cutoff then k c (L c hc hL) else 0
  else 0

noncomputable def totalLeafComponent (L : NativeLeafTapes sel r hm)
    (k : (c : Call (PhysicalHost f ell))→EncodedLeaf hm c→ℕ) (H : ℕ) : ℕ :=
  ∑ d∈Finset.range (H+1),((occurrences (Plan sel) r d).map (leafComponent sel r hm L k)).sum

theorem actual_leaf_components (L : NativeLeafTapes sel r hm) (c : Call (PhysicalHost f ell)) :
    leafComponent sel r hm L (fun _ D=>D.run.steps) c≤
      leafComponent sel r hm L (fun _ D=>D.directBill) c+
      leafComponent sel r hm L (fun _ D=>D.arithmeticCap) c := by
  classical
  by_cases hc : NativeReach (Plan sel) r c
  · by_cases hL : c.edges≤(S).cutoff
    · simp only [leafComponent,dif_pos hc,dif_pos hL]
      exact (L c hc hL).bill.2
    · simp [leafComponent,hc,hL]
  · simp [leafComponent,hc]

theorem list_bill_sum {X : Type*} (xs : List X) (a b c : X→ℕ)
    (h : ∀ x,a x≤b x+c x) :
    (xs.map a).sum≤(xs.map b).sum+(xs.map c).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x
    simp only [List.map_cons,List.sum_cons]
    omega

theorem total_leaf_bill (L : NativeLeafTapes sel r hm) (H : ℕ) :
    totalLeafComponent sel r hm L (fun _ D=>D.run.steps) H≤
      totalLeafComponent sel r hm L (fun _ D=>D.directBill) H+
      totalLeafComponent sel r hm L (fun _ D=>D.arithmeticCap) H := by
  unfold totalLeafComponent
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  apply list_bill_sum
  exact actual_leaf_components sel r hm L

include cfg in
theorem total_paid_tree_components (L : NativeLeafTapes sel r hm)
    (hr : Stable s C r) (d0 : r.depth=0) (p0 : r.prec≤C*s)
    (modeInputs : LayoutSupply (C:=C) sel r) :
    let H := pathLimit s C
    let mode := ∑ j∈Finset.range H,((occurrences (Plan sel) r j).map
      (builtCallCost cfg sel hr d0 p0 modeInputs)).sum
    let run := totalLeafComponent sel r hm L (fun _ D=>D.run.steps) H
    let exactEntries := totalLeafComponent sel r hm L (fun _ D=>D.directBill) H
    let arithmetic := totalLeafComponent sel r hm L (fun _ D=>D.arithmeticCap) H
    mode+run≤H*comboFee s C*2^(prefixConstant C *J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
      +exactEntries+arithmetic := by
  dsimp only
  have hMode := total_built_printed_rate cfg sel hr d0 p0 modeInputs
  have hLeaf := total_leaf_bill sel r hm L (pathLimit s C)
  exact (Nat.add_le_add hMode hLeaf).trans (by rw [Nat.add_assoc])

end Ledger
#print axioms EncodedLeaf.bill
#print axioms encoded_leaf_is_source_stop
#print axioms total_leaf_bill
#print axioms total_paid_tree_components
end J6R21Ancestor




