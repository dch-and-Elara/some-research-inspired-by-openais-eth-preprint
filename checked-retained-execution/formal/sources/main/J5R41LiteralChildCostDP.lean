import J5R41LiteralChildCostAxes
import J5R41LiteralChildCostMatching

/-! Native J5 compiler: construct one finite table from the original
child at ζ=0 and reuse it when reading any legal source-only tuple
supported by the fixed mode roster. The old stored weights are read
at their actual retained precision. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R11Blueprint J6R9Recursive
open J6R9PacketScopes J6R9PacketChild J6R9PacketTiles
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G) (t : ℤ)
variable (p : ℕ) (hnil : (2:Residue f ell p)^p=0)
variable (old : EntryFile f ell N) (hf : f.Monic)
variable (req : Finset (Mode i p P.mask))

def boundaryPort (m : Boundary P i g t) : Σ b : ColVertex P i g,ColPort P i g b :=
  (colChart P i g).symm (boundaryCol P i g t m)

def matchingLink (b : RowVertex P i g) (q : RowPort P i g b) : Option (Boundary P i g t) :=
  rowLink P i g t (rowChart P i g ⟨b,q⟩)

theorem actual_boundary_inputs (X : ColAssignments P i g) :
    JointContraction.matchedBits (boundaryPort P i g t) X =
      fun q => colAssignmentsEquiv P i g X (boundaryCol P i g t q) := rfl

theorem actual_row_product (Y : RowAssignments P i g) (X : ColAssignments P i g) :
    (∏ r : RowHalf P i g,affineAt (t:=t) P i g p hnil (pairedState P i g (Y,X)) r) =
      ∏ b : RowVertex P i g,∏ q : RowPort P i g b,
        JointContraction.literal (Y b q)
          (JointContraction.wiredInput (centreUnit (a:=a) t p hnil)
            (JointContraction.matchedBits (boundaryPort P i g t) X) (matchingLink P i g t b q)) := by
  let F := fun q : Σ b : RowVertex P i g,RowPort P i g b =>
        JointContraction.literal (Y q.1 q.2)
          (JointContraction.wiredInput (centreUnit (a:=a) t p hnil)
            (JointContraction.matchedBits (boundaryPort P i g t) X) (matchingLink P i g t q.1 q.2))
  rw [←Fintype.prod_sigma F]
  refine (Fintype.prod_equiv (rowChart P i g) F _ ?_).symm
  rintro ⟨b,q⟩
  dsimp only [F]
  rw [affine_at_boundary P i g t p hnil,new_state_row_reads P i g Y X b q,actual_boundary_inputs P i g t]
  rfl

/-- One table, determined once by the source chart, old file, centre,
and requested additive *coordinates*. Its construction does not take β. -/
def literalTable (roster : List (ColVertex P i g)) : J45Cost.Box (spanAt P i req)→Residue f ell p :=
  J45Cost.combinedTable (spanAt P i req) roster (boundaryPort P i g t) (matchingLink P i g t)
    (centreUnit (a:=a) t p hnil) (rowTable P i g p old hf) (colTable P i g p old hf)
    (J45Cost.sourceIncrement (sourceWeight P i g req))

variable (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (allSource : ∀ m∈req, source P.mask i m=g)

include allSource in
/-- Exact readout of a real native child from the one source-only
table. The orientation, chart, and old file are unchanged. -/
theorem actual_legal_child_from_table
    (roster : List (ColVertex P i g)) (hn : roster.Nodup) (ha : ∀ b, b∈roster)
    (β : LegalTuple P i p) (noTarget : HasNoTarget P i p β.val g)
    (covers : ∀ m, source P.mask i m=g → β.val m≠0 → m∈req) :
    physicalReply P i ht hv p hnil old hf β.val g =
      (letI : DecidableEq (Axis P i req) := Classical.decEq _
       ∑ x : J45Cost.Box (spanAt P i req),
        literalTable P i g t p hnil old hf req roster x *
          momentRead (f:=f) (ell:=ell) P i req β.val (J45Cost.intIndex (spanAt P i req) x)) := by
  have bd (X : ColAssignments P i g) (u : Axis P i req) :
      (∑ b,J45Cost.sourceIncrement (sourceWeight P i g req) b (X b)) u ≤ spanAt P i req u := by
    rw [←source_limit_actual P i g req allSource u]
    exact J45Cost.source_increment_bound (sourceWeight P i g req) X u
  have ha' : @List.toFinset (ColVertex P i g) (Classical.decEq _) roster=Finset.univ := by
    ext b
    simp [ha b]
  letI : DecidableEq (Axis P i req) := Classical.decEq _
  have dp := J45Cost.combinedTable_exact (spanAt P i req) roster hn ha'
    (boundaryPort P i g t) (matchingLink P i g t) (centreUnit (a:=a) t p hnil)
    (rowTable P i g p old hf) (colTable P i g p old hf)
    (J45Cost.sourceIncrement (sourceWeight P i g req)) (momentRead (f:=f) (ell:=ell) P i req β.val) bd
  let L {x y : Residue f ell p} (_ : x=y) := x
  let R {x y : Residue f ell p} (_ : x=y) := y
  refine (show _=R dp from ?_).trans ((show L dp=R dp from dp).symm.trans ?_)
  swap
  · dsimp only [L]
    unfold literalTable
    exact Finset.sum_congr (Finset.ext (fun x=>by simp)) (fun _ _=>rfl)
  dsimp only [R]
  rw [actual_child_real_support P i g p hnil req allSource ht hv old hf β noTarget covers]
  let F := fun v : PhysicalState P i g =>
    oldState P i g p old hf v *
      ((∏ r : RowHalf P i g,affineAt (t:=t) P i g p hnil v r) *
       ∏ m∈req,(sourceStat P i g v.2 m:Residue f ell p)^β.val m)
  have hsum : (∑ v : PhysicalState P i g,F v)=
      ∑ z : (RowAssignments P i g) × (ColAssignments P i g), F (pairedState P i g z) :=
    (Fintype.sum_equiv (pairedState P i g) _ _ (fun _=>rfl)).symm
  change (∑ v,F v)=_
  rw [hsum,Fintype.sum_prod_type,Finset.sum_comm]
  refine Finset.sum_congr (Finset.ext (fun x=>by simp)) fun X _=>?_
  refine Finset.sum_congr (Finset.ext (fun y=>by simp)) fun Y _=>?_
  unfold F
  rw [old_vertex_tables_realized P i g p old hf Y X,actual_row_product P i g t p hnil Y X]
  rw [actual_coordinate_readout P i g req β.val X]
  have hX : (pairedState P i g (Y,X)).2=colAssignmentsEquiv P i g X := rfl
  rw [hX]
  ring

#print axioms boundaryPort
#print axioms actual_boundary_inputs
#print axioms actual_row_product
#print axioms actual_legal_child_from_table
end
end J5R41LiteralChildCost

