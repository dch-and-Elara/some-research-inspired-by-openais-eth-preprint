import J4R43LiteralOutsideBoundaryFee
import J6ChildPlan

/-! Stream the actual matched-bit cube. The trace visits each
assignment once and needs only one branch-recursion stack rather than
a materialized cube. The local table-read fees are the literal
source addresses from BoundaryFee. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes J6R10RowAffine
open J5R41LiteralChildCost
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6300000

structure StreamRun (R : Type) where
  result : R
  visits : ℕ
  sums : ℕ
  frames : ℕ

def streamCube {R : Type} [AddCommMonoid R] :
    (n : ℕ)→((Fin n→Bool)→R)→StreamRun R
  | 0,f => ⟨f Fin.elim0,1,0,1⟩
  | n+1,f =>
    let lo := streamCube n (fun z=>f (Fin.cons false z))
    let hi := streamCube n (fun z=>f (Fin.cons true z))
    ⟨lo.result+hi.result,lo.visits+hi.visits,lo.sums+hi.sums+1,max lo.frames hi.frames+1⟩

theorem stream_cube_exact {R : Type} [AddCommMonoid R] (n : ℕ) (f : (Fin n→Bool)→R) :
    (streamCube n f).result=J6ChildPlan.allBits n f ∧
      (streamCube n f).visits=2^n ∧ (streamCube n f).sums=2^n-1 ∧
      (streamCube n f).frames=n+1 := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    let l := fun z=>f (Fin.cons false z)
    let r := fun z=>f (Fin.cons true z)
    let lo := streamCube n l
    let hi := streamCube n r
    have a := ih l
    have b := ih r
    refine ⟨?_,?_,?_,?_⟩
    · change lo.result+hi.result=J6ChildPlan.allBits n l+J6ChildPlan.allBits n r
      exact congrArg₂ (·+·) a.1 b.1
    · change lo.visits+hi.visits=(2:ℕ)^(n+1)
      rw [show lo.visits=2^n from a.2.1,show hi.visits=2^n from b.2.1,pow_succ]
      omega
    · change lo.sums+hi.sums+1=(2:ℕ)^(n+1)-1
      rw [show lo.sums=2^n-1 from a.2.2.1,show hi.sums=2^n-1 from b.2.2.1,pow_succ]
      have g : 0<(2:ℕ)^n := by positivity
      omega
    · change max lo.frames hi.frames+1=n+1+1
      rw [show lo.frames=n+1 from a.2.2.2,show hi.frames=n+1 from b.2.2.2,max_self]

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G) (t : ℤ)
variable (p : ℕ) (hnil : (2:Residue f ell p)^p=0)
variable (old : EntryFile f ell N) (hf : f.Monic)

def literalBoundaryTerm (w : Boundary P i g t→Bool) : Residue f ell p :=
  letI : DecidableEq (Boundary P i g t) := Classical.decEq _
  let port := boundaryPort P i g t
  let wire := matchingLink P i g t
  let c := centreUnit (a:=a) t p hnil
  JointContraction.rowValue wire c (rowTable P i g p old hf) w *
    ∏ b : ColVertex P i g,∑ x : ColPort P i g b→Bool,
      if JointContraction.agrees port w b x then colTable P i g p old hf b x else 0

def literalGraphDFS : StreamRun (Residue f ell p) :=
  let en := Fintype.equivFin (Boundary P i g t)
  streamCube _ (fun b=>literalBoundaryTerm P i g t p hnil old hf (b ∘ en))

theorem dfs_evaluates_one_native_group (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (hp : 0<p) :
    let run := literalGraphDFS P i g t p hnil old hf
    physicalReply P i ht hv p hnil old hf 0 g=run.result ∧
      run.visits=2^(matched P i g t).card ∧ run.sums=2^(matched P i g t).card-1 ∧
      run.frames=(matched P i g t).card+1 := by
  let en := Fintype.equivFin (Boundary P i g t)
  let n := Fintype.card (Boundary P i g t)
  let E := literalBoundaryTerm P i g t p hnil old hf
  let EE : (Fin n→Bool)→Residue f ell p := fun b=>E (b ∘ en)
  have k := stream_cube_exact n EE
  have exactValue : J6ChildPlan.allBits n EE=groupBoundaryValue P i g t p hnil old hf := by
    rw [J6ChildPlan.allBits_exact]
    let e := Equiv.arrowCongr en.symm (Equiv.refl Bool)
    have q : (∑ b : Fin n→Bool,EE b) = ∑ b : Boundary P i g t→Bool,E b := by
      apply Fintype.sum_equiv e EE E
      intro z
      rfl
    refine q.trans ?_
    unfold groupBoundaryValue
    exact Finset.sum_congr (Finset.ext fun _=>by simp) (fun _ _=>rfl)
  have hcard : n=(matched P i g t).card := Fintype.card_coe _
  refine ⟨?_,?_,?_,?_⟩
  · exact (literal_group_boundary_exact P i g p hnil old hf ht hv hp).trans
      (k.1.trans exactValue).symm
  · exact k.2.1.trans (congrArg (fun m : ℕ=>(2:ℕ)^m) hcard)
  · exact k.2.2.1.trans (congrArg (fun m : ℕ=>(2:ℕ)^m-1) hcard)
  · exact k.2.2.2.trans (congrArg (fun m : ℕ=>m+1) hcard)

#print axioms stream_cube_exact
#print axioms dfs_evaluates_one_native_group
end
end J4R43LiteralOutside

