import J6R34ChildPathChart

/-! Port conservation is not a conservation assertion about vertices.
The genuine child still has every physical Page as a column, even
when there is no selected parent half-port at that Page. -/
namespace J6R36RouteConservation
open scoped Polynomial
open Polynomial P11FullPacking J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath J6R21Ancestor J6ActiveRun
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 2300

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

noncomputable def physicalChildColumn : v.child.host.Col ≃ PageAt T v :=
  Equiv.cast (congrArg PhysicalHost.Col (actual_ticket_host T v))

private theorem right_cast {X Y : PhysicalHost f ell} (h : X=Y) (c : X.Col) :
    Equiv.cast (congrArg (fun H : PhysicalHost f ell=>H.Row⊕H.Col) h) (.inr c)=
      .inr (Equiv.cast (congrArg PhysicalHost.Col h) c) := by
  subst Y
  rfl

theorem actual_child_column_names_page (col : v.child.host.Col) :
    childVertices T v (.inr col)=.inr (physicalChildColumn T v col) :=
  right_cast (actual_ticket_host T v) col

theorem actual_incident_column_is_parent_packet (ed : v.child.host.Edge) :
    physicalChildColumn T v (v.child.host.network.col ed)=
      atPacket (layout T v) (edge (childHalves T v ed).val) := by
  have e := (actual_child_half_endpoints T v ed).2
  rw [actual_child_column_names_page] at e
  exact Sum.inr.inj e

theorem exact_page_incidence (k : PageAt T v) :
    (∃ ed : v.child.host.Edge,v.child.host.network.col ed=(physicalChildColumn T v).symm k) ↔
      ∃ u : HalfAt T v,atPacket (layout T v) (edge u.val)=k := by
  constructor
  · rintro ⟨ed,he⟩
    refine ⟨childHalves T v ed,?_⟩
    rw [←actual_incident_column_is_parent_packet T v ed,he,Equiv.apply_symm_apply]
  · rintro ⟨u,he⟩
    let ed := (childHalves T v).symm u
    refine ⟨ed,(physicalChildColumn T v).injective ?_⟩
    rw [Equiv.apply_symm_apply,actual_incident_column_is_parent_packet]
    change atPacket (layout T v) (edge ((childHalves T v) ((childHalves T v).symm u)).val)=k
    rw [Equiv.apply_symm_apply,he]

theorem zero_degree_page_stays_a_column (k : PageAt T v)
    (unused : ∀ u : HalfAt T v,atPacket (layout T v) (edge u.val)≠k) :
    ∃! col : v.child.host.Col, childVertices T v (.inr col)=.inr k ∧
      ∀ ed : v.child.host.Edge,v.child.host.network.col ed≠col := by
  let col := (physicalChildColumn T v).symm k
  have canon : physicalChildColumn T v col=k := (physicalChildColumn T v).apply_symm_apply k
  refine ⟨col,⟨(actual_child_column_names_page T v col).trans (congrArg Sum.inr canon),?_⟩,?_⟩
  · intro ed h
    obtain ⟨u,eq⟩ := (exact_page_incidence T v k).mp ⟨ed,h⟩
    exact unused u eq
  · intro a h
    apply (physicalChildColumn T v).injective
    rw [canon]
    have z := h.1
    rw [actual_child_column_names_page] at z
    exact Sum.inr.inj z

theorem even_zero_degree_page_has_its_created_entry (k : PageAt T v) :
    (entry (bornPoint T v k)).created=v.child.prec :=
  rfl

end J6R36RouteConservation
#print axioms J6R36RouteConservation.actual_child_column_names_page
#print axioms J6R36RouteConservation.actual_incident_column_is_parent_packet
#print axioms J6R36RouteConservation.exact_page_incidence
#print axioms J6R36RouteConservation.zero_degree_page_stays_a_column
#print axioms J6R36RouteConservation.even_zero_degree_page_has_its_created_entry
