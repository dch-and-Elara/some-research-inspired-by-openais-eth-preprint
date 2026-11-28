import J6R34ChildPathOrdinal
import J6R33StatefulArithmeticPageLeaf

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2200
set_option maxHeartbeats 9400000

/-! The same native leaf executor may use the *paid* chosen order on
its edges. It loops over all Boolean assignments and its physical
contraction does not depend on the earlier arbitrary equivFin.
This does not reorder a stored tape or assume those orders equal. -/
namespace J6R34ChildPath
open scoped BigOperators Polynomial Classical
open Polynomial AOracleMachineTime AOracleCoordinates A1R10 A1R11 A1R12
open J6ActiveRun J6R9Recursive J6R10Repack J6R11Blueprint J6R24MeteredRecursion
open J6R21Leaf J6R22Active J6R33StatefulArithmeticPage

theorem actual_paged_leaf_physical_order {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    {c : Call (PhysicalHost f ell)} (D : PagedLeaf c key page)
    (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : PageBank f ell key prec tw bw page) (ord : Fin c.edges≃c.host.Edge)
    (entryLaw : ∀ (x : Fin c.edges→Bool) v, F.decode (D.query hf F hEll B v (List.ofFn x)).result=
      (c.host.file v).read hf c.prec (assignment c.host.network (x∘ord.symm) v)) :
    F.decode (D.execute hf F hEll B).result=reduce c.prec f ell (c.host.contract hf) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let ι := literalChart (ell:=ell) F.exactMod
  let eval (x : c.host.Edge→Bool) :=
    ∏ v : c.host.Row⊕c.host.Col,
      (c.host.file v).read hf c.prec (assignment c.host.network x v)
  have fm (y : Block F ell) : F.decode y=ι (uvRead F.hp F.words ell y) :=
    (boxTransport_cast F.exactMod _).trans (literalChart_is_cast F.exactMod _).symm
  calc
    F.decode (D.execute hf F hEll B).result=∑ x : Fin c.edges→Bool,eval (x∘ord.symm) := by
      rw [fm,PagedLeaf.execute,clocked_leaf_is_native_enumerator F.hp F.sizePos hEll D.nodes _ D.clock D.clockShape,
        leafCompute,enumerate_exact,J6ChildPlan.allBits_exact,map_sum]
      simp only [List.reverse_nil,List.nil_append]
      apply Finset.sum_congr rfl
      intro x _
      rw [(readProduct_exact_and_billed F.hp F.sizePos hEll D.nodes (D.query hf F hEll B) (List.ofFn x)).1,
        map_list_prod,List.map_map]
      have eqset : D.nodes.toFinset=(Finset.univ : Finset (c.host.Row⊕c.host.Col)) :=
        Finset.ext (by intro v; simp [D.complete v])
      rw [← List.prod_toFinset _ D.unique,eqset]
      apply Finset.prod_congr rfl
      intro v _
      exact (fm _).symm.trans (entryLaw x v)
    _ = ∑ y : c.host.Edge→Bool,eval y := by
      apply Fintype.sum_equiv (ord.arrowCongr (Equiv.refl Bool))
      intro x
      rfl
    _ = _ := by
      unfold PhysicalHost.contract trueContraction
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [map_prod]
      rfl

#print axioms actual_paged_leaf_physical_order
end J6R34ChildPath
