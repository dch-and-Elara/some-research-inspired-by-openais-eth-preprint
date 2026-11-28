import J6R57LeafCapStored

/-! Pricing the stored leaf from its installed roster, without introducing
a separate vertex-name choice or fee table into the upper bound. -/
namespace J6R57LeafCap
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 J6R22Active J6R15ModeCost
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R10Repack J6R21Ancestor J6R21Leaf J6R24MeteredRecursion J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34ChildPath
open J6R48Leaf J6R50Leaf J6R51Leaf J6R50SourceProducer
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 22000000
set_option maxRecDepth 4300
set_option linter.unusedSectionVars false
set_option Elab.async false

private theorem zip_each_own_name {A B : Type*} (xs : List A) (f : A→B) :
    xs.zip (xs.map f) = xs.map (fun x=>(x,f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.zip_cons_cons,ih]

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "L" => (PageBank f ell key prec tw bw page)

def footprintExistingRows (site : StoredSite T v key prec tw bw page)
    (data : Unit→ResidentLeafData site) (D : RawTape v.child key page) : ℕ :=
  if v.child.edges=0 then 0 else
    ((D.rows.zip (data ()).roster).map (fun x=>
      rowSyntaxBuildFee v.child.edges (data ()).lines (data ()).table x.2 x.1.2+7)).sum

theorem prep_fee_is_installed_roster
    (site : StoredSite T v key prec tw bw page) (data : Unit→ResidentLeafData site)
    (D : RawTape v.child key page) (name : v.child.host.Row⊕v.child.host.Col→J6R15ModeCost.Word (data ()).own)
    (roster : 0<v.child.edges → (data ()).roster=D.rows.map (name∘Prod.fst)) :
    storedPrepShapeFee site data D name=footprintExistingRows site data D := by
  unfold storedPrepShapeFee footprintExistingRows
  by_cases e : v.child.edges=0
  · rw [if_pos e,if_pos e]
  · rw [if_neg e,if_neg e,roster (Nat.pos_of_ne_zero e),zip_each_own_name,List.map_map]
    rfl

def storedLeafInputScale (site : StoredSite T v key prec tw bw page)
    (data : Unit→ResidentLeafData site) (F : Frame f v.child.prec)
    (B : L) (D : RawTape v.child key page) : ℕ :=
  bookShapeFee site+4*v.child.edges+18+footprintExistingRows site data D+
    rawLeafScale F.words.length ell v.child.prec v.child.edges D.rows.length (prepriced D F B) F.hp

theorem stored_leaf_cap_from_literal_roster
    (site : StoredSite T v key prec tw bw page) (data : Unit→ResidentLeafData site)
    (F : Frame f v.child.prec) (pos : 0<ell) (B : L) (D : RawTape v.child key page)
    (format : HasResidentFormat D B) (H : ℕ) (stop : v.child.edges≤H)
    (checked : 0<v.child.edges→
      let keys (j : Fin v.child.edges) :=
        childKey T v site.birth.native.physical (actualEdgeOrder T v site.birth.native.physical j)
      ∃ name : v.child.host.Row⊕v.child.host.Col→J6R15ModeCost.Word (data ()).own,
      (data ()).roster=D.rows.map (name∘Prod.fst) ∧
      ∀ x∈D.rows, SourceCommand v.child.edges keys (data ()).lines (data ()).table (name x.1) x.2) :
    let old := runTape D hf F pos B
    let out := storedLeaf site data F pos B (fun _=>old)
    out.result=old.result ∧ out.steps≤2^H*storedLeafInputScale site data F B D := by
  by_cases e : v.child.edges=0
  · let name : v.child.host.Row⊕v.child.host.Col→J6R15ModeCost.Word (data ()).own := fun _=>J6R15ModeCost.word 0
    have exFalse (h : 0<v.child.edges) : False :=
      (Nat.ne_of_gt h) e
    have cost := actual_stored_leaf_has_structural_cap site data F pos B D format H stop name
      (fun h=>(exFalse h).elim)
    rw [prep_fee_is_installed_roster site data D name (fun h=>(exFalse h).elim)] at cost
    exact cost
  · obtain ⟨name,names,rows⟩ := checked (Nat.pos_of_ne_zero e)
    have cost := actual_stored_leaf_has_structural_cap site data F pos B D format H stop name
      (fun _=>⟨names,rows⟩)
    rw [prep_fee_is_installed_roster site data D name (fun _=>names)] at cost
    exact cost

#print axioms footprintExistingRows
#print axioms prep_fee_is_installed_roster
#print axioms storedLeafInputScale
#print axioms stored_leaf_cap_from_literal_roster
end
end J6R57LeafCap
