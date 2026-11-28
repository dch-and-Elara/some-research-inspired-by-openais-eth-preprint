import J6R34ChildPathOrdinal

/-! On a named Appendix D child, the actual emitted order enumerates
independent parent *occurrences*, with Boolean row/column side retained.
The byte statement is about the same R34 edge-book scan/copy; it does
not supply or infer a new raw ancestry body. -/
namespace J6R36RouteConservation
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 2200

/-- This is a projection to the type of original edge occurrences,
not to a pair of vertices. False = parent row; true = parent column. -/
def portIdentity (E : Type) : Port E ≃ E × Bool where
  toFun u := (edge u,side u)
  invFun p := if p.2 then .inr p.1 else .inl p.1
  left_inv := by rintro (e|e) <;> rfl
  right_inv := by rintro ⟨e,b⟩; cases b <;> rfl

variable {f : ℤ[X]} {ell s C w : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)
variable (D : PhysicalPorts sel (ticketReady T v) v.centerAt w)

noncomputable def indexedHalf : Fin v.child.edges ≃ HalfAt T v :=
  (actualEdgeOrder T v D).trans (childHalves T v)

noncomputable def indexedIdentity (j : Fin v.child.edges) : v.parent.host.Edge×Bool :=
  portIdentity _ (indexedHalf T v D j).val

theorem indexed_identity_injective : Function.Injective (indexedIdentity T v D) :=
  (portIdentity _).injective.comp (Subtype.val_injective.comp (indexedHalf T v D).injective)

theorem indexed_parent_exists_unique (p : Port v.parent.host.Edge)
    (h : physicalGroup sel (ticketReady T v) v.centerAt p=v.groupAt) :
    ∃! j : Fin v.child.edges, indexedIdentity T v D j=portIdentity _ p := by
  let q : HalfAt T v := ⟨p,h⟩
  let j := (indexedHalf T v D).symm q
  have same : indexedIdentity T v D j=portIdentity _ p :=
    congrArg (fun a : HalfAt T v=>portIdentity _ a.val) ((indexedHalf T v D).apply_symm_apply q)
  refine ⟨j,same,?_⟩
  intro k hk
  exact indexed_identity_injective T v D (hk.trans same.symm)

theorem indexed_parent_iff (p : Port v.parent.host.Edge) :
    (∃ j : Fin v.child.edges, indexedIdentity T v D j=portIdentity _ p) ↔
      physicalGroup sel (ticketReady T v) v.centerAt p=v.groupAt := by
  constructor
  · rintro ⟨j,h⟩
    have he : (indexedHalf T v D j).val=p := (portIdentity _).injective h
    rw [←he]
    exact (indexedHalf T v D j).property
  · intro h
    obtain ⟨j,hj,_⟩ := indexed_parent_exists_unique T v D p h
    exact ⟨j,hj⟩

variable {port edgeW depth prec tc tz tm : ℕ}
variable (J : NativeJob T v port edgeW depth prec tc tz tm)

theorem native_book_names_parent_side :
    let out := selectedEdgeBook J.gWord J.physical.raw
    out.result=List.ofFn (fun j : Fin v.child.edges=>
      (J.physical.record ((portIdentity _).symm (indexedIdentity T v J.physical j))).address) ∧
      out.result.Nodup ∧
      out.steps≤7+(J.physical.raw.map J6R25PreparedSupply.rowScanFee).sum+
        v.child.edges*(4*port+5) := by
  obtain ⟨book,dup,fee⟩ := exact_child_edge_book T v J
  refine ⟨book.trans ?_,dup,fee⟩
  apply congrArg List.ofFn
  funext j
  simp only [indexedIdentity,Equiv.symm_apply_apply]
  rfl

theorem native_book_address_at (j : Fin v.child.edges) :
    (selectedEdgeBook J.gWord J.physical.raw).result[j.val]? =
      some ((J.physical.record (indexedHalf T v J.physical j).val).address) := by
  have book := (native_book_names_parent_side T v J).1
  rw [book,List.getElem?_ofFn]
  simp only [j.isLt,dif_pos,indexedIdentity,Equiv.symm_apply_apply]

end J6R36RouteConservation
#print axioms J6R36RouteConservation.indexed_identity_injective
#print axioms J6R36RouteConservation.indexed_parent_exists_unique
#print axioms J6R36RouteConservation.indexed_parent_iff
#print axioms J6R36RouteConservation.native_book_names_parent_side
#print axioms J6R36RouteConservation.native_book_address_at
