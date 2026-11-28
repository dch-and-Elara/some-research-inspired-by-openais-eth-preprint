import J5R41LiteralChildCostDP
import J5R41LiteralChildCostParityAxes

/-! The parity menu of the same original native child at ζ=0.
The original beta tuple is not readdressed: the value, old tables
and row factor are projected to precision one after the chart is fixed. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2900000

theorem map_wired_literal {R R' M : Type*} [CommRing R] [CommRing R']
    (φ : R→+*R') (b : Bool) (unit : R) (x : M→Bool) (wire : Option M) :
    φ (JointContraction.literal b (JointContraction.wiredInput unit x wire)) =
    JointContraction.literal b (JointContraction.wiredInput (φ unit) x wire) := by
  cases b <;> cases wire with
  | none => simp [JointContraction.literal,JointContraction.wiredInput]
  | some j => cases h : x j <;> simp [JointContraction.literal,JointContraction.wiredInput,h]

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G) (t : ℤ)
variable (p : ℕ) (hnil : (2:Residue f ell p)^p=0) (hp : 1≤p)
variable (old : EntryFile f ell N) (hf : f.Monic)

def parityTable (roster : List (ColVertex P i g)) : Finset (Tile P i×Bool)→Residue f ell 1 :=
  let φ := J6R10Reachable.lower 1 p hp f ell
  weightedParityTable roster (boundaryPort P i g t) (matchingLink P i g t)
    (φ (centreUnit (a:=a) t p hnil))
    (fun b Y=>φ (rowTable P i g p old hf b Y))
    (fun b X=>φ (colTable P i g p old hf b X)) (allOdd P i g)

variable (ht : t≠0) (hv : padicValInt 2 t=i.val)

theorem actual_legal_child_parity
    (req : Finset (Mode i p P.mask)) (allSource : ∀ m∈req,source P.mask i m=g)
    (roster : List (ColVertex P i g)) (hn : roster.Nodup) (ha : ∀ b, b∈roster)
    (β : LegalTuple P i p) (noTarget : HasNoTarget P i p β.val g)
    (covers : ∀ m, source P.mask i m=g → β.val m≠0 → m∈req) :
    J6R10Reachable.lower 1 p hp f ell (physicalReply P i ht hv p hnil old hf β.val g) =
      J45Parity.run (parityTable P i g t p hnil hp old hf roster)
        (Finset.univ : Finset (Tile P i×Bool)).toList (parityRoster P i req β.val) := by
  let φ := J6R10Reachable.lower 1 p hp f ell
  have e := actual_child_real_support P i g p hnil req allSource ht hv old hf β noTarget covers
  rw [e]
  have ha' : @List.toFinset (ColVertex P i g) (Classical.decEq _) roster=Finset.univ := by
    ext b
    simp [ha b]
  unfold parityTable
  rw [weighted_parity_menu roster hn ha' (boundaryPort P i g t) (matchingLink P i g t)
    (φ (centreUnit (a:=a) t p hnil))
    (fun b Y=>φ (rowTable P i g p old hf b Y)) (fun b X=>φ (colTable P i g p old hf b X))
    (allOdd P i g) (parityEmbed f ell)]
  let F := fun v : PhysicalState P i g =>
    oldState P i g p old hf v *
      ((∏ r : RowHalf P i g,affineAt (t:=t) P i g p hnil v r) *
       ∏ m∈req,(sourceStat P i g v.2 m:Residue f ell p)^β.val m)
  have hsum : (∑ v : PhysicalState P i g,F v)=
      ∑ z : (RowAssignments P i g) × (ColAssignments P i g), F (pairedState P i g z) :=
    (Fintype.sum_equiv (pairedState P i g) _ _ (fun _=>rfl)).symm
  change φ (∑ v,F v)=_
  rw [hsum,Fintype.sum_prod_type,Finset.sum_comm,map_sum]
  simp_rw [map_sum]
  refine Finset.sum_congr (Finset.ext (fun x=>by simp)) fun X _=>?_
  refine Finset.sum_congr (Finset.ext (fun y=>by simp)) fun Y _=>?_
  unfold F
  rw [old_vertex_tables_realized P i g p old hf Y X,actual_row_product P i g t p hnil Y X]
  simp only [map_mul,map_prod,map_pow,map_natCast,map_wired_literal]
  have hX : (pairedState P i g (Y,X)).2=colAssignmentsEquiv P i g X := rfl
  rw [hX,actual_child_moment_parity (f:=f) (ell:=ell) P i g req β.val X]
  ring

def fullSourceRoster : Finset (Mode i p P.mask) :=
  Finset.univ.filter (fun m=>source P.mask i m=g)

theorem actual_complete_parity_menu
    (roster : List (ColVertex P i g)) (hn : roster.Nodup) (ha : ∀ b, b∈roster)
    (β : LegalTuple P i p) (noTarget : HasNoTarget P i p β.val g) :
    J6R10Reachable.lower 1 p hp f ell (physicalReply P i ht hv p hnil old hf β.val g) =
      J45Parity.run (parityTable P i g t p hnil hp old hf roster)
        (Finset.univ : Finset (Tile P i×Bool)).toList
          (parityRoster P i (fullSourceRoster P i g p) β.val) :=
  actual_legal_child_parity P i g t p hnil hp old hf ht hv _ (fun _ hm=>(Finset.mem_filter.mp hm).2)
    roster hn ha β noTarget (fun m hs _=> Finset.mem_filter.mpr ⟨Finset.mem_univ m,hs⟩)

#print axioms map_wired_literal
#print axioms actual_legal_child_parity
#print axioms actual_complete_parity_menu
end
end J5R41LiteralChildCost

