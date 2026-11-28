import J6R52TerminalMixed

/-! The literal leaf loop can be verified on raw commands directly;
there is no need to choose a new typed chart that re-encodes already
computed command bytes. -/
namespace J6R53TerminalGate
open scoped BigOperators Polynomial Classical
open Polynomial AOracleMachineTime AOracleCoordinates A1R10 A1R11 A1R12
open J6ActiveRun J6R9Recursive J6R10Repack J6R11Blueprint J6R24MeteredRecursion
open J6R21Leaf J6R22Active J6R33StatefulArithmeticPage J6R50Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 3300
set_option Elab.async false

theorem exact_raw_terminal_physical_order {f : ℤ[X]} {ell key prec tw bw page : ℕ}
    {c : Call (PhysicalHost f ell)}
    (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : PageBank f ell key prec tw bw page) (ord : Fin c.edges≃c.host.Edge)
    (clock : List Unit) (width : clock.length=c.edges)
    (nodes : List (c.host.Row⊕c.host.Col)) (unique : nodes.Nodup) (complete : ∀ v,v∈nodes)
    (cmd : c.host.Row⊕c.host.Col→ReadCmd key page)
    (entryLaw : ∀ (x : Fin c.edges→Bool) v,
      F.decode ((cmd v).read hf F hEll B (List.ofFn x)).result=
        (c.host.file v).read hf c.prec (assignment c.host.network (x∘ord.symm) v)) :
    F.decode (runRows hf F hEll B clock (nodes.map cmd)).result=reduce c.prec f ell (c.host.contract hf) := by
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
    F.decode (runRows hf F hEll B clock (nodes.map cmd)).result=∑ x : Fin c.edges→Bool,eval (x∘ord.symm) := by
      rw [fm,runRows,clocked_leaf_is_native_enumerator F.hp F.sizePos hEll (nodes.map cmd) _ clock width,
        leafCompute,enumerate_exact,J6ChildPlan.allBits_exact,map_sum]
      simp only [List.reverse_nil,List.nil_append]
      apply Finset.sum_congr rfl
      intro x _
      rw [readProduct_mapped F.hp F.sizePos hEll]
      rw [(readProduct_exact_and_billed F.hp F.sizePos hEll nodes
        ((fun r : ReadCmd key page=>r.read hf F hEll B)∘cmd) (List.ofFn x)).1,map_list_prod,List.map_map]
      have eqset : nodes.toFinset=(Finset.univ : Finset (c.host.Row⊕c.host.Col)) :=
        Finset.ext (by intro v; simp [complete v])
      rw [← List.prod_toFinset _ unique,eqset]
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

#print axioms exact_raw_terminal_physical_order
end J6R53TerminalGate
