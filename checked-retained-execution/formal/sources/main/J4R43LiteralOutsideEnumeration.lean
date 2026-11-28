import J5R41LiteralChildCostDP
import V8PooledMenuSlots
import J4R43LiteralOutsideGeometry

/-! The general zero-probe enumeration, independent of the favourable
outside-band order. It contracts only the actual matched words and
the genuine old vertex tables at their recorded creation precision. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes J6R10RowAffine
open J5R41LiteralChildCost
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3700000

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G) (t : ℤ)
variable (p : ℕ) (hnil : (2:Residue f ell p)^p=0)
variable (old : EntryFile f ell N) (hf : f.Monic)

def zeroTuple (hp : 0<p) : LegalTuple P i p :=
  ⟨0,(J6RecursiveMenu.exact_printed_menu p (weight i p P.mask)
    (fun m=>Nat.zero_lt_succ m.order.val) 0).mpr (by simpa [J6RecursiveMenu.weighted] using hp)⟩

def groupBoundaryValue : Residue f ell p :=
  letI : DecidableEq (Boundary P i g t) := Classical.decEq _
  let c := centreUnit (a:=a) t p hnil
  let port := boundaryPort P i g t
  let wire := matchingLink P i g t
  ∑ w : Boundary P i g t→Bool,
    JointContraction.rowValue wire c (rowTable P i g p old hf) w *
      ∏ b : ColVertex P i g,∑ x : ColPort P i g b→Bool,
        if JointContraction.agrees port w b x then colTable P i g p old hf b x else 0

variable {t} (ht : t≠0) (hv : padicValInt 2 t=i.val)

theorem literal_group_boundary_exact (hp : 0<p) :
    physicalReply P i ht hv p hnil old hf 0 g =
      groupBoundaryValue P i g t p hnil old hf := by
  have support := actual_child_real_support P i g p hnil ∅
    (fun m hm=>False.elim (Finset.notMem_empty m hm))
    ht hv old hf (zeroTuple P i p hp) (fun _ _=>rfl) (fun _ _ h=>False.elim (h rfl))
  simp only [Finset.prod_empty,mul_one] at support
  change physicalReply P i ht hv p hnil old hf 0 g = _ at support
  have actual := JointContraction.zero_probe_contraction (boundaryPort P i g t) (matchingLink P i g t)
    (centreUnit (a:=a) t p hnil) (rowTable P i g p old hf) (colTable P i g p old hf)
  let L {x y : Residue f ell p} (_ : x=y) := x
  let R {x y : Residue f ell p} (_ : x=y) := y
  refine support.trans ((show _=L actual from ?_).trans ((show L actual=R actual from actual).trans ?_))
  · dsimp only [L]
    let F := fun v : PhysicalState P i g =>
      oldState P i g p old hf v * ∏ r : RowHalf P i g,affineAt (t:=t) P i g p hnil v r
    have e : (∑ v : PhysicalState P i g,F v)=
        ∑ z : (RowAssignments P i g) × (ColAssignments P i g), F (pairedState P i g z) :=
      (Fintype.sum_equiv (pairedState P i g) _ _ (fun _=>rfl)).symm
    change (∑ v,F v)=_
    rw [e,Fintype.sum_prod_type,Finset.sum_comm]
    refine Finset.sum_congr (Finset.ext (fun x=>by simp)) fun X _=>?_
    refine Finset.sum_congr (Finset.ext (fun y=>by simp)) fun Y _=>?_
    dsimp only [F]
    rw [old_vertex_tables_realized P i g p old hf Y X,actual_row_product P i g t p hnil Y X]
    ac_rfl
  · dsimp only [R]
    unfold groupBoundaryValue
    refine Finset.sum_congr (Finset.ext (fun x=>by simp)) fun w _=>?_
    congr 1
    refine Finset.prod_congr (Finset.ext (fun v=>by simp)) fun v _=>?_
    exact Finset.sum_congr (Finset.ext (fun v=>by simp)) (fun _ _=>rfl)

theorem literal_whole_boundary_exact (hp : 0<p) :
    V8PooledMenu.slot P i ht hv p hnil 0 old hf 0 =
      ∏ g : G,groupBoundaryValue P i g t p hnil old hf := by
  unfold V8PooledMenu.slot
  refine Finset.prod_congr rfl fun g _=>?_
  exact literal_group_boundary_exact P i g p hnil old hf ht hv hp

theorem literal_nonzero_completed_mode_at_zero (β : Mode i p P.mask→₀ℕ) (nz : β≠0) :
    V8PooledMenu.slot P i ht hv p hnil 0 old hf β=0 := by
  obtain ⟨m,hm⟩ : ∃ m,β m≠0 := by
    by_contra! h
    apply nz
    ext m
    exact h m
  unfold V8PooledMenu.slot
  let g := (target P.mask i m).2
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  exact actual_positive_target_child_zero P i ht hv p hnil old hf β g m rfl hm

#print axioms zeroTuple
#print axioms literal_group_boundary_exact
#print axioms literal_whole_boundary_exact
#print axioms literal_nonzero_completed_mode_at_zero
end
end J4R43LiteralOutside

