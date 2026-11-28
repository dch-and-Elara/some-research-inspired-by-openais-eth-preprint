import J6R25PreparedSupplyPhysicalPorts

set_option autoImplicit false

/-! The R26 descriptor schema by itself does not certify ancestry
bodies. Even valid, complete occurrence rows with all exact address
and group words can carry an arbitrary body. -/
namespace J6R34ChildPath
open scoped Classical Polynomial
open J6ActiveRun J6R11Blueprint J6R12Blueprint J6R10Repack J1PPrinted
open J6R25PreparedSupply J6R15ModeCost

variable {f : ℤ[X]} {ell s w : ℕ}
  {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
  {c : Call (PhysicalHost f ell)}
  {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
  {t : Center (printedParams (f:=f) (ell:=ell) s) c}

def setBodies (D : PhysicalPorts sel d t w) (bytes : Port c.host.Edge→List Bool) :
    PhysicalPorts sel d t w where
  raw := D.order.map (fun u=>{D.record u with body:=bytes u})
  order := D.order
  nodup := D.nodup
  complete := D.complete
  record := fun u=>{D.record u with body:=bytes u}
  source := rfl
  labelled := D.labelled
  distinct := D.distinct

theorem physical_rows_do_not_fix_body (D : PhysicalPorts sel d t w)
    (u : Port c.host.Edge) (payload : List Bool) (hn : payload≠[]) :
    ∃ bad : PhysicalPorts sel d t w,
      bad.order=D.order ∧
      (∀ x,(bad.record x).address=(D.record x).address ∧ (bad.record x).group=(D.record x).group) ∧
      u∈bad.physicalSelected (physicalGroup sel d t u) ∧ (bad.record u).body≠payload := by
  let bad := setBodies D (fun _=>[])
  refine ⟨bad,rfl,fun _=>⟨rfl,rfl⟩,?_,Ne.symm hn⟩
  exact List.mem_filter.mpr ⟨bad.complete u,decide_eq_true rfl⟩

#print axioms physical_rows_do_not_fix_body
end J6R34ChildPath
