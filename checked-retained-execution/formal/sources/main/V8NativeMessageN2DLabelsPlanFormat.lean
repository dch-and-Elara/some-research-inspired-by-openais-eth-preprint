import V8NativeMessageN2DLabelsSelector
import J6R14LayoutCostAxes

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000
set_option linter.unusedSectionVars false

/-! A complete format can be obtained from the actual finite graph.
The executable part below takes explicit ordinal charts. A second,
noncomputable instantiation uses logical equivFin; it does not promise
to serialize raw vertex names or to choose the original machine order. -/
namespace V8NativeMessage.N2DLabels
open scoped Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionGreedyStep J6R12CollisionMenu J6R14LayoutCost
open J6R10Repack J6R11Blueprint J6ActiveRun J6R12Blueprint

def ordinalWidth (n : ℕ) := Nat.clog 2 (n+1)

theorem ordinal_fits (n : ℕ) : n<2^ordinalWidth n :=
  Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) (n+1))

private theorem complete_of_equiv {A : Type*} {n : ℕ} (ord : Fin n≃A) (u : A) :
    u∈List.ofFn ord :=
  List.mem_ofFn.mpr ⟨ord.symm u,ord.apply_symm_apply u⟩

variable {E R C : Type*} [Fintype E] [Fintype R] [Fintype C]

structure GraphOrders (E R C : Type*) [Fintype E] [Fintype R] [Fintype C] where
  edges : E≃Fin (Fintype.card E)
  rows : R≃Fin (Fintype.card R)
  cols : C≃Fin (Fintype.card C)

def GraphOrders.vertexOrder (O : GraphOrders E R C) :
    Fin (Fintype.card R+Fintype.card C)≃R⊕C :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr O.rows.symm O.cols.symm)

/-- The only additional input beyond finite actual graph data is the
three explicit orders. Endpoint maps, named edge roster, alphabet
word, dimensions, and combined vertex order are generated here. -/
def formatFromOrders (N : Network E R C) (a : ℕ) (O : GraphOrders E R C) :
    Full64Input N a where
  format :=
    { e := ordinalWidth (Fintype.card E)
      kR := ordinalWidth (Fintype.card R)
      kC := ordinalWidth (Fintype.card C)
      b := 6*a
      rCode := fun r=>(O.rows r).val
      cCode := fun c=>(O.cols c).val
      aCode := fun x=>bitsValue (coordinateLabel x)
      rInj := fun _ _ h=>O.rows.injective (Fin.ext h)
      cInj := fun _ _ h=>O.cols.injective (Fin.ext h)
      aInj := by
        intro x y hv
        apply coordinateLabel_inj
        exact equal_width_inj (by rw [coordinateLabel_len,coordinateLabel_len]) hv
      rFit := fun r=>(O.rows r).isLt.trans (ordinal_fits _)
      cFit := fun c=>(O.cols c).isLt.trans (ordinal_fits _)
      aFit := fun x=>by rw [←coordinateLabel_len x]; exact bitsValue_lt _
      edgesFit := ordinal_fits _
      alphabetFit := (source_alphabet (Fintype.card_fin 64) a).le
      row := N.row
      col := N.col
      edges := List.ofFn O.edges.symm
      edgesNodup := List.nodup_ofFn.mpr O.edges.symm.injective
      edgesAll := complete_of_equiv O.edges.symm }
  rowExact := rfl
  colExact := rfl
  labelWidth := rfl
  order := List.ofFn O.vertexOrder
  distinct := List.nodup_ofFn.mpr O.vertexOrder.injective
  complete := complete_of_equiv O.vertexOrder

theorem format_coordinates (N : Network E R C) (a : ℕ) (O : GraphOrders E R C)
    (x : Fin a→Fin 64) : (formatFromOrders N a O).format.label x=coordinateLabel x := by
  let F := (formatFromOrders N a O).format
  apply equal_width_inj
  · change (encodeBits (6*a) (bitsValue (coordinateLabel x))).length=(coordinateLabel x).length
    rw [encodeBits_length,coordinateLabel_len]
  · change bitsValue (encodeBits (6*a) (bitsValue (coordinateLabel x)))=bitsValue (coordinateLabel x)
    exact encodeBits_exact _ _ (F.aFit x)

theorem format_actual_incidence (N : Network E R C) (a : ℕ) (O : GraphOrders E R C) :
    (formatFromOrders N a O).raw=
      List.ofFn (fun k=>(
        encodeBits (ordinalWidth (Fintype.card R)) (O.rows (N.row (O.edges.symm k))).val,
        encodeBits (ordinalWidth (Fintype.card C)) (O.cols (N.col (O.edges.symm k))).val)) := by
  unfold Full64Input.raw
  change (List.ofFn O.edges.symm).map _=_
  rw [List.map_ofFn]
  rfl

noncomputable def logicalGraphOrders (E R C : Type*) [Fintype E] [Fintype R] [Fintype C] :
    GraphOrders E R C :=
  ⟨Fintype.equivFin E,Fintype.equivFin R,Fintype.equivFin C⟩

section Host
variable {f : ℤ[X]} {ell : ℕ}

abbrev HostOrders (H : PhysicalHost f ell) :=
  @GraphOrders H.Edge H.Row H.Col H.finiteEdge H.finiteRow H.finiteCol

def formatOfHost {S : Params (f:=f) (ell:=ell)} (c : Call (PhysicalHost f ell))
    (orders : HostOrders c.host) : CallFormat S c := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  exact formatFromOrders c.host.network (S.levelBits c.depth) orders

noncomputable def logicalHostOrders (H : PhysicalHost f ell) : HostOrders H :=
  @logicalGraphOrders H.Edge H.Row H.Col H.finiteEdge H.finiteRow H.finiteCol

/-- At the typed semantic level there is no remaining supplied format
family. The ordinals are logical choices on the actual graph; a machine
claim needs the genuine graph ordinals/order and their byte producers. -/
noncomputable def logicalFormats (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) :
    Full64PlanInputs S Δ :=
  fun c _ => formatOfHost c (logicalHostOrders c.host)
end Host

#print axioms ordinal_fits
#print axioms format_coordinates
#print axioms format_actual_incidence
#print axioms formatOfHost
#print axioms logicalFormats
end V8NativeMessage.N2DLabels
